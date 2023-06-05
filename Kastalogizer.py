"""
Kastalogizer
Jan Hartman, 1. rocnik, cviceni streda od 16:30
Zimni semestr 2022/23
Programovani NPRG030

Tento program resi problem hledani daneho kastanu z N kastanu pomoci vazeni na dvouramennych vahach. 
Kastan ktery hledame musi splnovat podminku, ze alespon A kastanu je lehcich nez on a alespon 
B kastanu je tezsich. 

Hlavni vstup programu predavame jako trojici cisel N A B. Dale program umoznuje zadat
prednastavenou posloupnost vazeni, kterou musi program brat jako predpoklad vypoctu.
Dale program na vstupu umoznuje zadat, ruzne moznosti upravy efektivity prohledavani a nebo
zda-li chceme tisknout statistiky o behu programu po nalezeni vysledku.

Vystupem programu je cislo udavajici minimalni pocet potrebnych vazeni v nejhorsim pripade,
dale cislo udavajici index nalezeneho kastanu a v neposledni rade posloupnost vazeni,
ktere program vykonal, aby dany kastan nalezl. Posloupnost vazeni je vypisovana jako 
posloupnost dvojic kastanu. Prvky kazde dvojice kastanu jsou oddeleny znaminkem vetsi nez, 
ktere znaci, ktery z kastanu vaha vyhodnotila jako ten tezsi.

"""

import time

""" Promenne, jejichz hodnotu ziskame od uzivatele na vstupu """
kastanuCelkem = 0 # uchovava celkovy pocet kastanu
kolikLehcich = 0 # uchovava informaci o tom, alespon kolik kastanu musi byt lehci nez hledany kastan
kolikTezsich = 0 # alespon kolik musi byt tezsi nez hledany

""" Priznaky, ktere ziskame od uzivatele uzivatele na vstupu """
chciOsekatVyberNeznamych = False # priznak ktery rika, zda-li budeme v nasem programu odsekavat izomorfni vybery dvojic na zvazeni
chciOsekavatProhozenaPoradi = False # priznak ktery udava, zda-li bude program odsekavat pripady volby stejnych kombinaci vazeni hracem akorat v jinem poradi
chciTisknoutStatistiky = False # priznak ktery udava, zda spolu s vysledkem budeme tisknout i dalsi pomocne statistiky
chciOdsekavatBUNORozhodnutiVahy = False # priznak, ktery rika jestli budeme odrezavat pripady, kdy muze vaha bez ujmy na obbecnosti jakkoliv rozhodnout

""" Promenna inicializovana na zacatku programu na zaklade zadanych dat uzivatele a po zbytek behu programu se nemeni """
limitVazeni = 0 # maximalni mozny pocet potrebnych vazeni. Slouzi jako horni mez poctu moznych vazeni, ktery se hrac snazi minimalizovat

""" Promenne, ktere slouzi jako pocitadla pro pomocne statistiky o programu """
pocitadloListu = 0 # debugovaci promenna, ktera udava kolikrat se rekurzivni funkce zanori az na dno
pocitadloIdentickychVyberuNeznamych = 0 # pocita kolikrat program odsekl pripad, kdy jsme opakovane chteli zvazit neznamy kastan s nejakym uz zvazenym znamym
pocitadloAlfaBeta = 0 # pocita, koilkrat program alfa beta prorizl nejakou vetev
pocitadloJinehoPoradi = 0 # pocita, kolikrat program odrizl vetev se stejnou kombinaci vazeni avsak v jinem poradi
pocitadloBUNORozhodnutiVahy = 0 # pocita, kolikrat program odsekl vetev, ve ktere nezalezelo na vysledku vyberu viteze a porazeneho
    # toto nastane, pokud kastany, ktere hodlam vazit maji napriklad oba stupen 0, v tom pripade nezalezi na tom, ktery kastan vaha vybrala
    # jako tezsi, jelikoz vysledne grafy relace byt tezsi nez budou k sobe navzajem izomorfni

""" Promenna, ktera je vyuzita pouze pokud se uzivatel rozhodne, ze chce zacit vypocet s vlastnimi prednastavenymi vysledky vazeni"""
pocatecniKonfiguraceVazeni = tuple() # slouzi k manualnimu nacteni vazeni, ktera si pak algoritmus musi vzit jako predpoklad vypoctu 

""" Promenne, ktere slouzi jako vstupni data pro minimaxovy algoritmus prochazejici strom hry """
vsechnyKombinaceKastanu = set() # mnozina, ve ktere mam ulozene kombinace kastanu, ktere jeste mohu zvazit (jelikoz o jejich vztahu zatim nic nevim) a postupne z ni odebiram
pocatecniMnozinaTezsich = [] # seznam mnozin, ktery uchovava informaci o tom, jake kastany jsou tezsi nez dany kastan
pocatecniMnozinaLehcich = [] # seznam mnozin, ktery uchovava informaci o tom, jake kastany jsou lehci nez dany kastan
pocatecniPocetVazeni = 0 # uchovava pocet doposud provedenych vazeni behem chodu programu
pocatecniAlfa = 0 # hodnota alfa, ktera slouzi k implementaci alfa beta prorezavani
pocatecniBeta = -1  # hodnota beta, ktera slouzi k implementaci alfa beta prorezavani
pocatecniNalezenyKastan = -1 # slouzi pro ulozeni indexu hledaneho kastanu po te, co je hledany kastan nalezen, hodnota -1 znaci, ze jeste nebyl nalezen
pocatecniHodnotaBinarniho = 0 # kontrolni binarni reprezentace, ktera se pocita prekodovanim z provedenych vazeni. Stejna provedena vazeni akorat v jinem poradi vraci stejnou sumu

""" Promenna, ktera obsahuje slovnik s predpocitanymi mezivysledky, ktere mohu nasledne pouzit v jinych vetvich stromu hry """
spocitaneKombinaceVazeni = dict() # globalni slovnik, ktery pro danou kombinaci dvojic kastanu uklada nejmensi mozny pocet vazeni, kdyz tato vazeni provedu.
    # Slouzi k tomu, abych vypocet pro stejnou kombinaci dvojic kastanu akorat v jinem poradi nemusel provadet znovu.
    # Vysledek si tedy zapamatuji pote, co ho poprve spocitam a v dalsich pripadech uz mohu tento vysledek vracet v konstantnim case.
    # Jako klic pro tento slovnik slouzi kodovaci binarni reprezentace, ktera vraci pro kazdou permutaci vyberu kastanu stejny vysledek nehlede na poradi

""" Pomocna tabulka obsahujici unikatni identifikacni cislo pro kazdou usporadanou dvojici kastanu"""
kodovaniDvojic = dict() # Tento slovnik umoznuje provest vypocet pomocne binarni reprezentace, ktera pak identifikuje urcitou kombinaci dvojic kastanu na zvazeni

def nactiKonfiguraciVazeniZeVstupu():
    """
    Pokud chce uzivatel prednacist provedena vazeni ze vstupu a spocitat, jak ma vazit dale za
    tohoto predpokladu, tak tato funkce zjisti, jakou posloupnost vazeni si uzivatel preje zadat.
    Tato funkce take predpocita seznamy mnozin tezsich a lehcich kastanu aby obsahovaly
    informace o vahach kastanu, ktere ziskame z prednastavenych vazeni.
    """

    global pocatecniKonfiguraceVazeni, pocatecniMnozinaTezsich, pocatecniMnozinaLehcich, vsechnyKombinaceKastanu, pocatecniPocetVazeni, pocatecniNalezenyKastan
    
    pocatecniNalezenyKastan = -1 # nastavime hodnotu nalezeneho kastanu na pocatecni

    vytvorSeznamyMnozinTezsichALehcich() # vytvorime nove prazdne seznamy mnozin lehcich a tezsich kastanu
    vygenerujKombinace() # stejne tak si znovu vygenerujeme vsechny kombinace kastanu, ktere jeste potrebujeme zvazit

    while True:  # tato smycka skonci pouze v pripade, ze je zadan spravny vstup a tudiz se program dostane na prikaz break
        try:
            seznam = [int(x) for x in input("Zadej postupne vsechny dvojice indexu kastanu, ktere chces zvazit predem: ").split()]
            for  cislo in seznam:
                if cislo < 0 or cislo >= kastanuCelkem:
                    raise ValueError(f"Kastan s indexem {cislo} neexistuje!")
            if len(seznam) % 2 != 0:
                raise ValueError("Pocet kastanu na vaze musi byt sude cislo!")
            if len(seznam) > 2 * limitVazeni:
                raise ValueError("To je trochu moc vazeni nemyslis?")
            pocatecniKonfiguraceVazeni = tuple()
            for i in range(0,len(seznam),2):
                if seznam[i] == seznam[i+1]:
                    raise ValueError(f"Kastan s indexem {seznam[i]} neni mozne polozit na obe ramena vahy!")
                pocatecniKonfiguraceVazeni = pocatecniKonfiguraceVazeni + ((seznam[i],seznam[i+1]),)
            pocatecniPocetVazeni = len(pocatecniKonfiguraceVazeni)

            # nasledujici smycka aktualizuje mnoziny tezsich a lehcich kastanu na zaklade uzivatelem prednastavenych vazeni
            for vazeni in pocatecniKonfiguraceVazeni:
                hledanyKastan = zvazAktualizujMnozinyAVratHledanyKastan(vazeni[0],vazeni[1],pocatecniMnozinaTezsich,pocatecniMnozinaLehcich,vsechnyKombinaceKastanu)
                if hledanyKastan != -1: # pokud zadana uzivatelova vazeni vedla k tomu, ze byl odhalen hledany kastan drive nez jsme vubec zacali vypocet minimaxu
                    pocatecniNalezenyKastan = hledanyKastan
            print(f"Zadal jsi pocatecni vazeni: {pocatecniKonfiguraceVazeni}")

            break # pokud vse probehlo bez erroru, tak se dostaneme na tento break a mame hotovo
        except ValueError as e:
            print(e)


def prectiCelyVstup():
    """ Precte vstup a ulozi ho do odpovidajicich promennych"""
    
    global kastanuCelkem, kolikLehcich, kolikTezsich, limitVazeni, pocatecniAlfa, chciOsekatVyberNeznamych, chciOsekavatProhozenaPoradi, chciTisknoutStatistiky, chciOdsekavatBUNORozhodnutiVahy

    print("\nVitej, tento uzasny program vyresi vsechny tve problemy tykajici se kastanu!")
    print("Ztratil se ti kastan s konkretni vahou v tve kolekci kastanu? Pomuzu ti ho najit!")
    print("Vytahni svou dvouramennou vahu a pak na vstupu zadej udaje o tve sbirce kastanu:")

    while True:
        try:
            try:
                vstup = [int(x) for x in input("\nZadej trojici cisel oddelenych mezerou (#Celkem #Lehcich #Tezsich): ").split()]
            except ValueError:
                raise ValueError("Na vstupu jsi zadal nejakou necelociselnou hodnotu")
            if len(vstup) != 3:
                raise ValueError("Zadal jsi nespravny pocet cisel")
            kastanuCelkem = vstup[0]
            if kastanuCelkem <= 0:
                raise ValueError("Pocet kastanu musi byt kladne cele cislo")
            limitVazeni = ((kastanuCelkem * (kastanuCelkem-1) ) // 2) + 1 # max bude vazeni tolik, kolik je pocet vsech dvouprvkovych kombinaci kastanu
            pocatecniAlfa = limitVazeni

            kolikLehcich = vstup[1]
            if kolikLehcich < 0:
                raise ValueError("Pocet lehcich kastanu nemuze byt zaporny")
            if kolikLehcich >= kastanuCelkem:
                raise ValueError("Lehcich kastanu nemuze byt stejne nebo vice, nez je jejich celkovy pocet")

            kolikTezsich = vstup[2]
            if kolikTezsich < 0:
                raise ValueError("Pocet tezsich kastanu nemuze byt zaporny")
            if kolikTezsich >= (kastanuCelkem-kolikLehcich):
                raise ValueError("Tezsich kastanu tolik byt nemuze")

            break # pokud se program dostal do tohoto bodu, tak cteni vstupu probehlo bez erroru

        except ValueError as e: # byla vytvorena nejaka vyjimka a telo smycky tedy pobezi znovu
            print(e)

    chciOsekatVyberNeznamych = nactiAnoNeVstup("Prejes si osekavat izomorfni vybery vazeni neznamych kastanu se znamymi? ano = 1, ne = 0: ")
    chciOsekavatProhozenaPoradi = nactiAnoNeVstup("Prejes si osekavat identicke kombinace vazeni akorat v jinem poradi? ano = 1, ne = 0: ")
    chciOdsekavatBUNORozhodnutiVahy = nactiAnoNeVstup("Prejes si odsekavat pripady, kdy vaha mohla rozhodnout ruzne bez ujmy na obecnosti? ano = 1, ne = 0: ")
    chciTisknoutStatistiky = nactiAnoNeVstup("Prejes si tisknout statistiky? ano = 1, ne = 0: ")
    prejiSiNacistPredvolbuVazeni = nactiAnoNeVstup("Prejes si nacist sva vlastni pocatecni vazeni? ano = 1, ne = 0: ")

    if prejiSiNacistPredvolbuVazeni:
        nactiKonfiguraciVazeniZeVstupu()
    else:
        vytvorSeznamyMnozinTezsichALehcich()
        vygenerujKombinace()
    
    konfigurujKodovaniDvojic()


def nactiAnoNeVstup(hlaseni):
    """
    Zepta se uzivatele na otazku ano ne, kterou predame funkci argumentem "hlaseni" a pote vrati bud True nebo False
    dle toho, co uzivatel zadal.
    """

    while True:
        try:
            try:
                vstup = int(input(hlaseni))
            except ValueError:
                raise ValueError("Zadana hodnota musi byt typu int")
            if vstup < 0 or vstup > 1:
                raise ValueError("Zadana hodnota musi lezet mezi 0 a 1 vcetne")
            if vstup == 1:
                return True
            else:
                return False
        except ValueError as e:
            print(e)


def konfigurujKodovaniDvojic():
    """ 
    Tato funkce pro dany pocet kastanu prirady kazde usporadane dvojici kastanu jedno unikatni cislo
    Toto unikatni cislo pak slouzi k tomu, aby se posloupnost dvojic (vazeni) kastanu dala zakodovat
    jako binarni cislo, ktere pak mohu porovnavat.
    """
    pocitadlo = 0
    for i in range(kastanuCelkem):
        for j in range(kastanuCelkem):
            kodovaniDvojic[(i,j)] = pocitadlo
            pocitadlo += 1


def prictiDvojiciKBinarnimuAVratNove(puvodniBinarni,dvojice):
    """
    Tato funkce aktualizuje kontrolni sumu o nove pridanou dvojici
    Kazda dvojice reprezentuje jedno vazeni. Stejna kombinace vazeni akorat v jine
    posloupnosti vygeneruje stejnou sumu. Pomoci teto sumy lze v konstantnim case
    zkontrolovat, zda-li se jedna o stejnou kombinaci akorat jinak zprehazenou.
    """
    return puvodniBinarni + (2 ** kodovaniDvojic[dvojice])


def vytvorSeznamyMnozinTezsichALehcich(): 
    """ 
    Tato funkce vytvori prazdne seznamy mnozin tezsich a lehcich kastanu
    Tyto mnoziny nacte do globalnich seznamu
    """
    global kastanuCelkem, pocatecniMnozinaTezsich, pocatecniMnozinaLehcich

    pocatecniMnozinaTezsich = []
    pocatecniMnozinaLehcich = []

    for i in range(kastanuCelkem):
        pocatecniMnozinaTezsich.append(set())
        pocatecniMnozinaLehcich.append(set())


def zvazAktualizujMnozinyAVratHledanyKastan(vitez, porazeny, mnozinaTezsich, mnozinaLehcich, zbyleKombinace):
    """ Po zvazeni dvou kastanu a vyhodnoceni viteze a porazeneho aktualizuje mnoziny, aby se zapocitala transitivita"""

    hledanyKastan = -1

    # toto je samotny vysledek vazeni kastanu, ktere jsme polozili na vahu
    aktualizujZbyleKombinace(vitez,porazeny,zbyleKombinace) # nejprve odstranime tyto kastany ze zbylych kombinaci, abychom je nevazili znovu
    vysledekVazeni = pridejDoMnozinAVratHledany(vitez,porazeny,mnozinaTezsich, mnozinaLehcich)
    if vysledekVazeni != -1:
        hledanyKastan = vysledekVazeni

    # tento for cyklus se stara o zapocteni tranzitivity
    for nadvitez in mnozinaTezsich[vitez]: # kastany, ktere jsou tezsi nez vitez jsou tezsi i nez porazeny
        aktualizujZbyleKombinace(nadvitez,porazeny,zbyleKombinace)
        vysledekVazeni = pridejDoMnozinAVratHledany(nadvitez,porazeny,mnozinaTezsich, mnozinaLehcich)
        if vysledekVazeni != -1:
            hledanyKastan = vysledekVazeni
        
        for podporazeny in mnozinaLehcich[porazeny]: # vsechny kastany, ktere jsou lehci nez porazeny musi byt lehci nez nadvitez
            aktualizujZbyleKombinace(nadvitez,podporazeny,zbyleKombinace)
            vysledekVazeni = pridejDoMnozinAVratHledany(nadvitez,podporazeny,mnozinaTezsich, mnozinaLehcich)
            if vysledekVazeni != -1:
                hledanyKastan = vysledekVazeni
        
    # toto musi byt samostatny for cyklus (uvazme pripad, kdy neni zadny nadvitez, ale existuje podporazeny)
    for podporazeny in mnozinaLehcich[porazeny]:  
        aktualizujZbyleKombinace(vitez,podporazeny,zbyleKombinace)
        vysledekVazeni = pridejDoMnozinAVratHledany(vitez,podporazeny,mnozinaTezsich, mnozinaLehcich)
        if vysledekVazeni != -1:
            hledanyKastan = vysledekVazeni

    return hledanyKastan


def aktualizujZbyleKombinace(tezsi,lehci,zbyleKombinace):
    """
        Aktualizuje seznam zbylych kombinaci na zvazeni, abychom nevazili dvojice, jejichz vztah uz zname
    """
    # pokud mame informaci o kastanech, ze jsou jeden tezsi a jeden lehci (treba i diky tranzitivite)
    # ,tak uz nemusime vazit tyto kastany znovu a tudiz je odebereme ze seznamu kombinaci na zvazeni
    
    # ve zbylich kombinacich je kastan s mensim indexem vzdy nalevo, proto nemusime zkouset odstranit oba zbusoby usporadani dvojice
    if tezsi < lehci:
        if (tezsi,lehci) in zbyleKombinace:
            zbyleKombinace.remove((tezsi,lehci))
    else:
        if (lehci,tezsi) in zbyleKombinace:
            zbyleKombinace.remove((lehci,tezsi))


def pridejDoMnozinAVratHledany(tezsi,lehci,mnozinaTezsich,mnozinaLehcich):
    """ Aktualizuje obe mnoziny lehcich i tezsich kastanu a take zkontroluje, jestli jde o hledany kastan.
        Funkce vraci index nalezeneho kastanu nebo -1 pokud jsme kastan jeste nenalezli
    """   
    # nyni aktualizujeme mnoziny tezsich a lehcich kastanu
    mnozinaTezsich[lehci].add(tezsi)
    if len(mnozinaTezsich[lehci]) >= kolikTezsich: # tento kastan uz ma dostatek tezsich kastanu
        if len(mnozinaLehcich[lehci]) >= kolikLehcich: # a dokonce ma i dostatek lehcich, takze mame hotovo
            return lehci

    mnozinaLehcich[tezsi].add(lehci)
    if len(mnozinaLehcich[tezsi]) >= kolikLehcich: # stejne jako predchozi pripad, ale obracene
       if len(mnozinaTezsich[tezsi]) >= kolikTezsich:
            return tezsi

    return -1


def vygenerujKombinace():
    """ Vygeneruje seznam vsech moznych kombinaci dvou kastanu (kazda kombinace reprezentuje jedno vazeni) 
        Tyto vygenerovane kombinace nacte do globalni mnoziny vsech kombinaci, ze kterych je 
        v prubehu programu postupne odebirano.
    """
    global vsechnyKombinaceKastanu
    vsechnyKombinaceKastanu = set()

    # tato cast funkce bezi v kvadratickem case vzhledem k poctu kastanu
    for i in range(kastanuCelkem):
        for j in range(i+1,kastanuCelkem):
            vsechnyKombinaceKastanu.add((i,j))


def zkopirujSeznamMnozin(starySeznam):
    """ Zajistuje deep copy cele datove struktury jmenem: seznam mnozin tezsich a lehcich kastanu"""
    novySeznam = []

    for i in range(kastanuCelkem):
        novySeznam.append(starySeznam[i].copy())

    return novySeznam


def tahHrace(mnozinaTezsich,mnozinaLehcich,zbyleKombinace,pocetVazeni,provedenaVazeni,binarni,alfa,beta):
    """
    Tato funkce reprezentuje tah hrace, ktery se snazi minimalizovat pocet vazeni nutnych k nalezeni hledaneho kastanu
    """
    global chciOsekatVyberNeznamych, pocitadloIdentickychVyberuNeznamych, pocitadloAlfaBeta
    
    # tato hodnota urcuje doposud nejmensi pocet moznych vazeni provedenych do tohoto stavu hry (tuto moznost si hrac vybere, jelikoz je pro nej nejlepsi)
    lokalniMinimum =  limitVazeni # potrebuji ji inicializovat na maximalni hodnotu, ktera se akorat v prubehu algoritmu bude snizovat
    nalezenyKastan = -1 # sem si ulozim nalezeny kastan pro nejlepsi volbu vazeni hrace
    optimalniVazeni = None # do teto promenne si ulozim posloupnost udelanych vazeni pro nejlepsi moznou volbu hrace

    # tato mnozina si uklada informace o znamych (mame o nich uz nejakou informaci) kastanech, se kterymi uz jsme vazili nejaky neznamy
    # vzdy staci vazit pouze s jednim neznamym, pokud je jich vice, jinak je vysledek totozny (nezname kastany jsou zamenitelne)
    vybraneZname = set()
    vybranyObaNezname = False # pokud vybirame dva nezname kastany, tak to staci udelat jenom jednou, jinak uz to nema smysl

    for kombinace in zbyleKombinace: # pro kazdou kombinaci kastanu, ktere je jeste potreba zvazit je zkus zvazit

        if chciOsekatVyberNeznamych:

            prvni = kombinace[0]
            druhy = kombinace[1]

            # ziskame vstupni a vystupni stupne obou kastanu (vstupni = # tezsich, vystupni = # lehcich)
            stupnePrvniho = (len(mnozinaTezsich[prvni]),len(mnozinaLehcich[prvni]))
            stupneDruheho = (len(mnozinaTezsich[druhy]),len(mnozinaLehcich[druhy]))

            # o techto kastanech jsme jeste neziskali zadnou informaci a jsou pro nas tedy nezname
            if stupnePrvniho == (0,0) and stupneDruheho == (0,0):
                if vybranyObaNezname: # uz jsme mezi sebou v teto vetvi jednou vazili dva zcela nezname kastany a to nam staci
                    pocitadloIdentickychVyberuNeznamych += 1
                    continue
                else:
                    vybranyObaNezname = True
            elif stupnePrvniho == (0,0) and stupneDruheho != (0,0): # prvni kastan je neznamy a druhy je znamy
                if druhy in vybraneZname:
                    pocitadloIdentickychVyberuNeznamych += 1
                    continue
                else:
                    vybraneZname.add(druhy)
            elif stupnePrvniho != (0,0) and stupneDruheho == (0,0): # prvni kastan je znamy a druhy je neznamy
                if prvni in vybraneZname:
                    pocitadloIdentickychVyberuNeznamych += 1
                    continue
                else:
                    vybraneZname.add(prvni)         

        # pridame do posloupnosti provedenych vazeni aktualni kombinaci, aby si ji potom vaha mohla podle sebe zpracovat
        novaProvedenaVazeni = provedenaVazeni + (kombinace,)
            
        mezivysledek = tahVahy(mnozinaTezsich,mnozinaLehcich,zbyleKombinace,pocetVazeni,novaProvedenaVazeni,binarni,alfa,beta)

        # protoze je na tahu hrac, tak si voli nejmensi mozny pocet nutnych vazeni a podle toho aktualizuje odpovidajici promenne
        if mezivysledek[0] < lokalniMinimum:
            lokalniMinimum = mezivysledek[0]
            nalezenyKastan = mezivysledek[1]
            optimalniVazeni = mezivysledek[2]

        # hodnota alfa udava doposud nejlepsi mozny pocet vazeni, ktery si hrac muze vybrat
        alfa = min(alfa,lokalniMinimum)

        # nejminimalnejsi mozna volba hrace je lepsi nez nejnepriznivejsi volba vahy
        if alfa <= beta: # prorizneme danou vetev
            pocitadloAlfaBeta += 1
            return (lokalniMinimum,nalezenyKastan,optimalniVazeni)
        
    return (lokalniMinimum,nalezenyKastan,optimalniVazeni)


def tahVahy(mnozinaTezsich,mnozinaLehcich,zbyleKombinace,pocetVazeni,provedenaVazeni,binarni,alfa,beta):
    """
    Tato funkce reprezentuje tah vahy, ktera se snazi maximalizovat pocet vazeni nutnych k nalezeni kastanu
    Funkce vraci v bazickem pripade usporadanou trojici hodnot
            1. Pocet vazeni, ktere jsme museli provest abychom nalezli hledany kastan
            2. Index hledaneho kastanu
            3. Posloupnost usporadanych dvojic indexu kastanu, kazda dvojice odpovida jednomu vazeni a jeho vysledku
                    (kastan vyhodnoceny jako tezsi je vzdy prvnim prvkem usporadane dvojice)
    """
    global pocitadloAlfaBeta, pocitadloListu, pocitadloJinehoPoradi, pocitadloBUNORozhodnutiVahy, chciOsekavatProhozenaPoradi

    lokalniMaximum = -1
    nalezenyKastan = -1
    optimalniVazeni = None # posloupnost vazeni provedena pro doposud nejlepsi volbu vahy

    # vytahneme si posledni prvek posloupnosti, ktery odpovida dvojici kastanu, ktere si hrac vybral na zvazeni (musime je nyni zvazit)
    kombinaceNaZvazeni = provedenaVazeni[len(provedenaVazeni)-1] 
    
    # vaha ted muze rozhodnout dvema zpusoby
    for i in range(2):

        
        if chciOdsekavatBUNORozhodnutiVahy and i == 0:
            stupnePrvniho = (len(mnozinaTezsich[kombinaceNaZvazeni[0]]),len(mnozinaLehcich[kombinaceNaZvazeni[0]]))
            stupneDruheho = (len(mnozinaTezsich[kombinaceNaZvazeni[1]]),len(mnozinaLehcich[kombinaceNaZvazeni[1]]))

            # pokud oba kastany, ktere zrovna hodlam vazit maji stejny stupen, tak nezalezi na vysledku vazeni
            # mohu tedy preskocit druhy vysledek vazeni
            if stupnePrvniho == (0,0) and stupneDruheho == (0,0):
                pocitadloBUNORozhodnutiVahy += 1
                continue

        hledanyKastan = -1

        # zvoli vysledek vazeni podle toho, jaka je hodnota promenne i 
        # nejprve je vitezem levy kastan kombinace, v druhem pruchodu cyklem je to pravy kastan
        vitez = kombinaceNaZvazeni[i]
        porazeny = kombinaceNaZvazeni[1-i]

        # nyni je treba vytvorit kopie techto datovych struktur, protoze se je chystame upravovat
        noveZbyleKombinace = zbyleKombinace.copy()
        novaMnozinaTezsich = zkopirujSeznamMnozin(mnozinaTezsich)
        novaMnozinaLehcich = zkopirujSeznamMnozin(mnozinaLehcich)

        # toto volani aktualizuje mnoziny a kombinace a vrati hledany kastan, pokud jsme ho nasli
        hledanyKastan = zvazAktualizujMnozinyAVratHledanyKastan(vitez,porazeny,novaMnozinaTezsich,novaMnozinaLehcich,noveZbyleKombinace)
        novaVazeni = provedenaVazeni[:len(provedenaVazeni)-1] + ((vitez,porazeny),)
        novaBinarni = 0

        # aktualizovanim mnoziny jsme nalezli hledany kastan
        if hledanyKastan != -1:
            pocitadloListu += 1
            mezivysledek = (pocetVazeni+1,hledanyKastan,provedenaVazeni)
        # stale jsme jeste nenasli hledany kastan a musime se rekurzivne zanorit a nebo vyuzit predpocitanych kombinaci vazeni
        else: 

            # pokud jsem si zadal volbu osekavani identickych kombinaci vazeni akorat s jinym poradim
            if chciOsekavatProhozenaPoradi:
                # chceme osekavat identicke kombinace, tak spocitame kod
                novaBinarni = prictiDvojiciKBinarnimuAVratNove(binarni,(vitez,porazeny))

                # mame stesti, tato vazeni uz jsme nekdy provadeli akorat v jinem poradi a vysledek si pamatujeme z minula
                if novaBinarni in spocitaneKombinaceVazeni: 
                    pocitadloJinehoPoradi += 1
                    mezivysledek = spocitaneKombinaceVazeni[novaBinarni]
                else: # bohuzel jsme jeste na stejna vazeni v jinem poradi nenarazili
                    mezivysledek = tahHrace(novaMnozinaTezsich,novaMnozinaLehcich,noveZbyleKombinace,pocetVazeni+1,novaVazeni,novaBinarni,alfa,beta)    
                    spocitaneKombinaceVazeni[novaBinarni] = mezivysledek
            else:
                mezivysledek = tahHrace(novaMnozinaTezsich,novaMnozinaLehcich,noveZbyleKombinace,pocetVazeni+1,novaVazeni,novaBinarni,alfa,beta)
            
        # vaha se snazi vratit co nejhorsi vysledek co se poctu vazeni tyce
        if mezivysledek[0] > lokalniMaximum:
            lokalniMaximum = mezivysledek[0]
            nalezenyKastan = mezivysledek[1]
            optimalniVazeni = mezivysledek[2]

        beta = max(beta,lokalniMaximum)

        # vaha vybere urcite horsi tah, nez je nejaky tah v jine vetvi pro hrace
        # tuto vetev tedy pro hrace nema smysl vybirat
        
        if alfa <= beta: # prorizneme tedy danou vetev
            pocitadloAlfaBeta += 1
            return (lokalniMaximum,nalezenyKastan,optimalniVazeni)
     
    return (lokalniMaximum,nalezenyKastan,optimalniVazeni)


def vytiskniPosloupnostVazeni():
    """Vytiskne nalezenou posloupnost vazeni v hezcim formatu"""

    global vysledek

    print("Posloupnost provedenych vazeni (tezsi > lehci): ",end="")
    for dvojice in vysledek[2]:
        print(f"{dvojice[0]} > {dvojice[1]}",end= " , ")


def vytiskniVysledek():
    """
    Tato funkce se stara o tisknuti vystupu programu
    """
    global vysledek, zacatekCasomiry, konecCasomiry

    print("\nZDE JE TVUJ VYSLEDEK:")
    print(f"Minimalni pocet potrebnych vazeni: {vysledek[0]}")
    print(f"Index nalezeneho kastanu: {vysledek[1]}")
    vytiskniPosloupnostVazeni()
    print()
    if chciTisknoutStatistiky:
        print(f"Pocet koncovych stavu pri prohledavani: {pocitadloListu:_}")
        print(f"Pocet alfa-beta prorezani: {pocitadloAlfaBeta:_}")
        if chciOsekatVyberNeznamych:
            print(f"Pocet odstranenych izomorfnich vyberu neznamych kastanu: {pocitadloIdentickychVyberuNeznamych:_}")
        if chciOsekavatProhozenaPoradi:
            print(f"Pocet odstranenych identickych kombinaci vazeni s jinym poradim: {pocitadloJinehoPoradi:_}")
        if chciOdsekavatBUNORozhodnutiVahy:
            print(f"Pocet odstranenych vetvi, ve kterych mohla vaha BUNO rozhodnout jakkoliv: {pocitadloBUNORozhodnutiVahy:_}")
        print(f"Doba behu vypoctu: {konecCasomiry-zacatekCasomiry} sekund")


def main():
    """
    Hlavni funkce programu
    """
    global zacatekCasomiry, vysledek, konecCasomiry, spocitaneKombinaceVazeni, pocatecniKonfiguraceVazeni, pocatecniNalezenyKastan

    prectiCelyVstup() # ziska od uzivatele vstupni data a nacte je do odpovidajicich globalnich promennych

    while True: # hlavni smycka programu, konci pokud jiz uzivatel nechce pro dane kastany volit jina prednastavena vazeni
        zacatekCasomiry = time.time()
        if pocatecniNalezenyKastan != -1: # prednactena vazeni vedla primo k vysledku
            vysledek = (pocatecniPocetVazeni,pocatecniNalezenyKastan,pocatecniKonfiguraceVazeni)
        else: # kastan jsme z prednactenych vazeni jeste nemohli urcit a musime spustit prohledavani stromu hry
            vysledek = tahHrace(pocatecniMnozinaTezsich,pocatecniMnozinaLehcich,vsechnyKombinaceKastanu,pocatecniPocetVazeni,pocatecniKonfiguraceVazeni,pocatecniHodnotaBinarniho,pocatecniAlfa,pocatecniBeta) 
        konecCasomiry = time.time()
        vytiskniVysledek()

        if nactiAnoNeVstup("\nPrejes si vyzkouset vypocet pro jinou pocatecni posloupnost vazeni? ano = 1, ne = 0:  "):
            nactiKonfiguraciVazeniZeVstupu()
            spocitaneKombinaceVazeni = dict() 
        else:
            print("Nashledanou")
            break

main()

""" 
TESTOVACI VSTUPY
-----------------
Nejtezsi ze tri: 3 2 0 -> 2
Prostredni z peti: 5 2 2 -> 6
Nejtezsi z peti: 5 4 0 -> 4
Druhy nejtezsi ze sesti: 6 4 1 -> 7
Nejtezsi ze sedmi: 7 6 0 -> 6 (trva cca 40 sekund na mem pocitaci)
"""
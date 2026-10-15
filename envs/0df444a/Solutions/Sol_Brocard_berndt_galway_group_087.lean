-- Prove2me | solution 1 for Brocard.berndt_galway_group_087
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:32:27.031262+00:00
-- url     : https://prove2.me/submissions/12e10ed0-c2f1-4699-93d1-56c7b326cbbf

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3987
import Theorems.Thm_Brocard_berndt_galway_chunk_3988
import Theorems.Thm_Brocard_berndt_galway_chunk_3989
import Theorems.Thm_Brocard_berndt_galway_chunk_3990
import Theorems.Thm_Brocard_berndt_galway_chunk_3991
import Theorems.Thm_Brocard_berndt_galway_chunk_3992
import Theorems.Thm_Brocard_berndt_galway_chunk_3993
import Theorems.Thm_Brocard_berndt_galway_chunk_3994
import Theorems.Thm_Brocard_berndt_galway_chunk_3995
import Theorems.Thm_Brocard_berndt_galway_chunk_3996
import Theorems.Thm_Brocard_berndt_galway_chunk_3997
import Theorems.Thm_Brocard_berndt_galway_chunk_3998
import Theorems.Thm_Brocard_berndt_galway_chunk_3999
import Theorems.Thm_Brocard_berndt_galway_chunk_4000
import Theorems.Thm_Brocard_berndt_galway_chunk_4001
import Theorems.Thm_Brocard_berndt_galway_chunk_4002
import Theorems.Thm_Brocard_berndt_galway_chunk_4003
import Theorems.Thm_Brocard_berndt_galway_chunk_4004
import Theorems.Thm_Brocard_berndt_galway_chunk_4005
import Theorems.Thm_Brocard_berndt_galway_chunk_4006
import Theorems.Thm_Brocard_berndt_galway_chunk_4007
import Theorems.Thm_Brocard_berndt_galway_chunk_4008
import Theorems.Thm_Brocard_berndt_galway_chunk_4009
import Theorems.Thm_Brocard_berndt_galway_chunk_4010
import Theorems.Thm_Brocard_berndt_galway_chunk_4011
import Theorems.Thm_Brocard_berndt_galway_chunk_4012
import Theorems.Thm_Brocard_berndt_galway_chunk_4013
import Theorems.Thm_Brocard_berndt_galway_chunk_4014
import Theorems.Thm_Brocard_berndt_galway_chunk_4015
import Theorems.Thm_Brocard_berndt_galway_chunk_4016
import Theorems.Thm_Brocard_berndt_galway_chunk_4017
import Theorems.Thm_Brocard_berndt_galway_chunk_4018
import Theorems.Thm_Brocard_berndt_galway_chunk_4019
import Theorems.Thm_Brocard_berndt_galway_chunk_4020
import Theorems.Thm_Brocard_berndt_galway_chunk_4021
import Theorems.Thm_Brocard_berndt_galway_chunk_4022
import Theorems.Thm_Brocard_berndt_galway_chunk_4023
import Theorems.Thm_Brocard_berndt_galway_chunk_4024
import Theorems.Thm_Brocard_berndt_galway_chunk_4025
import Theorems.Thm_Brocard_berndt_galway_chunk_4026
import Theorems.Thm_Brocard_berndt_galway_chunk_4027
import Theorems.Thm_Brocard_berndt_galway_chunk_4028
import Theorems.Thm_Brocard_berndt_galway_chunk_4029
import Theorems.Thm_Brocard_berndt_galway_chunk_4030
import Theorems.Thm_Brocard_berndt_galway_chunk_4031
import Theorems.Thm_Brocard_berndt_galway_chunk_4032
import Theorems.Thm_Brocard_berndt_galway_chunk_4033

theorem solution (n m : ℕ) (h1 : 716906474 ≤ n) (h2 : n < 725359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 721223021 with hs0 | hs0
  · -- n < 721223021
    rcases Nat.lt_or_ge n 719064748 with hs1 | hs1
    · -- n < 719064748
      rcases Nat.lt_or_ge n 717985611 with hs2 | hs2
      · -- n < 717985611
        rcases Nat.lt_or_ge n 717446043 with hs3 | hs3
        · -- n < 717446043
          rcases Nat.lt_or_ge n 717266187 with hs4 | hs4
          · -- n < 717266187
            rcases Nat.lt_or_ge n 717086330 with hs5 | hs5
            · -- n < 717086330
              exact Brocard.berndt_galway_chunk_3987 n m (by omega) (by omega) h
            · -- n >= 717086330
              exact Brocard.berndt_galway_chunk_3988 n m (by omega) (by omega) h
          · -- n >= 717266187
            exact Brocard.berndt_galway_chunk_3989 n m (by omega) (by omega) h
        · -- n >= 717446043
          rcases Nat.lt_or_ge n 717805755 with hs4 | hs4
          · -- n < 717805755
            rcases Nat.lt_or_ge n 717625899 with hs5 | hs5
            · -- n < 717625899
              exact Brocard.berndt_galway_chunk_3990 n m (by omega) (by omega) h
            · -- n >= 717625899
              exact Brocard.berndt_galway_chunk_3991 n m (by omega) (by omega) h
          · -- n >= 717805755
            exact Brocard.berndt_galway_chunk_3992 n m (by omega) (by omega) h
      · -- n >= 717985611
        rcases Nat.lt_or_ge n 718525179 with hs3 | hs3
        · -- n < 718525179
          rcases Nat.lt_or_ge n 718345323 with hs4 | hs4
          · -- n < 718345323
            rcases Nat.lt_or_ge n 718165467 with hs5 | hs5
            · -- n < 718165467
              exact Brocard.berndt_galway_chunk_3993 n m (by omega) (by omega) h
            · -- n >= 718165467
              exact Brocard.berndt_galway_chunk_3994 n m (by omega) (by omega) h
          · -- n >= 718345323
            exact Brocard.berndt_galway_chunk_3995 n m (by omega) (by omega) h
        · -- n >= 718525179
          rcases Nat.lt_or_ge n 718884892 with hs4 | hs4
          · -- n < 718884892
            rcases Nat.lt_or_ge n 718705035 with hs5 | hs5
            · -- n < 718705035
              exact Brocard.berndt_galway_chunk_3996 n m (by omega) (by omega) h
            · -- n >= 718705035
              exact Brocard.berndt_galway_chunk_3997 n m (by omega) (by omega) h
          · -- n >= 718884892
            exact Brocard.berndt_galway_chunk_3998 n m (by omega) (by omega) h
    · -- n >= 719064748
      rcases Nat.lt_or_ge n 720143884 with hs2 | hs2
      · -- n < 720143884
        rcases Nat.lt_or_ge n 719604316 with hs3 | hs3
        · -- n < 719604316
          rcases Nat.lt_or_ge n 719424460 with hs4 | hs4
          · -- n < 719424460
            rcases Nat.lt_or_ge n 719244604 with hs5 | hs5
            · -- n < 719244604
              exact Brocard.berndt_galway_chunk_3999 n m (by omega) (by omega) h
            · -- n >= 719244604
              exact Brocard.berndt_galway_chunk_4000 n m (by omega) (by omega) h
          · -- n >= 719424460
            exact Brocard.berndt_galway_chunk_4001 n m (by omega) (by omega) h
        · -- n >= 719604316
          rcases Nat.lt_or_ge n 719964028 with hs4 | hs4
          · -- n < 719964028
            rcases Nat.lt_or_ge n 719784172 with hs5 | hs5
            · -- n < 719784172
              exact Brocard.berndt_galway_chunk_4002 n m (by omega) (by omega) h
            · -- n >= 719784172
              exact Brocard.berndt_galway_chunk_4003 n m (by omega) (by omega) h
          · -- n >= 719964028
            exact Brocard.berndt_galway_chunk_4004 n m (by omega) (by omega) h
      · -- n >= 720143884
        rcases Nat.lt_or_ge n 720683453 with hs3 | hs3
        · -- n < 720683453
          rcases Nat.lt_or_ge n 720503597 with hs4 | hs4
          · -- n < 720503597
            rcases Nat.lt_or_ge n 720323741 with hs5 | hs5
            · -- n < 720323741
              exact Brocard.berndt_galway_chunk_4005 n m (by omega) (by omega) h
            · -- n >= 720323741
              exact Brocard.berndt_galway_chunk_4006 n m (by omega) (by omega) h
          · -- n >= 720503597
            exact Brocard.berndt_galway_chunk_4007 n m (by omega) (by omega) h
        · -- n >= 720683453
          rcases Nat.lt_or_ge n 721043165 with hs4 | hs4
          · -- n < 721043165
            rcases Nat.lt_or_ge n 720863309 with hs5 | hs5
            · -- n < 720863309
              exact Brocard.berndt_galway_chunk_4008 n m (by omega) (by omega) h
            · -- n >= 720863309
              exact Brocard.berndt_galway_chunk_4009 n m (by omega) (by omega) h
          · -- n >= 721043165
            exact Brocard.berndt_galway_chunk_4010 n m (by omega) (by omega) h
  · -- n >= 721223021
    rcases Nat.lt_or_ge n 723381294 with hs1 | hs1
    · -- n < 723381294
      rcases Nat.lt_or_ge n 722302158 with hs2 | hs2
      · -- n < 722302158
        rcases Nat.lt_or_ge n 721762589 with hs3 | hs3
        · -- n < 721762589
          rcases Nat.lt_or_ge n 721582733 with hs4 | hs4
          · -- n < 721582733
            rcases Nat.lt_or_ge n 721402877 with hs5 | hs5
            · -- n < 721402877
              exact Brocard.berndt_galway_chunk_4011 n m (by omega) (by omega) h
            · -- n >= 721402877
              exact Brocard.berndt_galway_chunk_4012 n m (by omega) (by omega) h
          · -- n >= 721582733
            exact Brocard.berndt_galway_chunk_4013 n m (by omega) (by omega) h
        · -- n >= 721762589
          rcases Nat.lt_or_ge n 722122302 with hs4 | hs4
          · -- n < 722122302
            rcases Nat.lt_or_ge n 721942446 with hs5 | hs5
            · -- n < 721942446
              exact Brocard.berndt_galway_chunk_4014 n m (by omega) (by omega) h
            · -- n >= 721942446
              exact Brocard.berndt_galway_chunk_4015 n m (by omega) (by omega) h
          · -- n >= 722122302
            exact Brocard.berndt_galway_chunk_4016 n m (by omega) (by omega) h
      · -- n >= 722302158
        rcases Nat.lt_or_ge n 722841726 with hs3 | hs3
        · -- n < 722841726
          rcases Nat.lt_or_ge n 722661870 with hs4 | hs4
          · -- n < 722661870
            rcases Nat.lt_or_ge n 722482014 with hs5 | hs5
            · -- n < 722482014
              exact Brocard.berndt_galway_chunk_4017 n m (by omega) (by omega) h
            · -- n >= 722482014
              exact Brocard.berndt_galway_chunk_4018 n m (by omega) (by omega) h
          · -- n >= 722661870
            exact Brocard.berndt_galway_chunk_4019 n m (by omega) (by omega) h
        · -- n >= 722841726
          rcases Nat.lt_or_ge n 723201438 with hs4 | hs4
          · -- n < 723201438
            rcases Nat.lt_or_ge n 723021582 with hs5 | hs5
            · -- n < 723021582
              exact Brocard.berndt_galway_chunk_4020 n m (by omega) (by omega) h
            · -- n >= 723021582
              exact Brocard.berndt_galway_chunk_4021 n m (by omega) (by omega) h
          · -- n >= 723201438
            exact Brocard.berndt_galway_chunk_4022 n m (by omega) (by omega) h
    · -- n >= 723381294
      rcases Nat.lt_or_ge n 724460431 with hs2 | hs2
      · -- n < 724460431
        rcases Nat.lt_or_ge n 723920863 with hs3 | hs3
        · -- n < 723920863
          rcases Nat.lt_or_ge n 723741007 with hs4 | hs4
          · -- n < 723741007
            rcases Nat.lt_or_ge n 723561151 with hs5 | hs5
            · -- n < 723561151
              exact Brocard.berndt_galway_chunk_4023 n m (by omega) (by omega) h
            · -- n >= 723561151
              exact Brocard.berndt_galway_chunk_4024 n m (by omega) (by omega) h
          · -- n >= 723741007
            exact Brocard.berndt_galway_chunk_4025 n m (by omega) (by omega) h
        · -- n >= 723920863
          rcases Nat.lt_or_ge n 724280575 with hs4 | hs4
          · -- n < 724280575
            rcases Nat.lt_or_ge n 724100719 with hs5 | hs5
            · -- n < 724100719
              exact Brocard.berndt_galway_chunk_4026 n m (by omega) (by omega) h
            · -- n >= 724100719
              exact Brocard.berndt_galway_chunk_4027 n m (by omega) (by omega) h
          · -- n >= 724280575
            exact Brocard.berndt_galway_chunk_4028 n m (by omega) (by omega) h
      · -- n >= 724460431
        rcases Nat.lt_or_ge n 725000000 with hs3 | hs3
        · -- n < 725000000
          rcases Nat.lt_or_ge n 724820143 with hs4 | hs4
          · -- n < 724820143
            rcases Nat.lt_or_ge n 724640287 with hs5 | hs5
            · -- n < 724640287
              exact Brocard.berndt_galway_chunk_4029 n m (by omega) (by omega) h
            · -- n >= 724640287
              exact Brocard.berndt_galway_chunk_4030 n m (by omega) (by omega) h
          · -- n >= 724820143
            exact Brocard.berndt_galway_chunk_4031 n m (by omega) (by omega) h
        · -- n >= 725000000
          rcases Nat.lt_or_ge n 725179856 with hs4 | hs4
          · -- n < 725179856
            exact Brocard.berndt_galway_chunk_4032 n m (by omega) (by omega) h
          · -- n >= 725179856
            exact Brocard.berndt_galway_chunk_4033 n m (by omega) (by omega) h

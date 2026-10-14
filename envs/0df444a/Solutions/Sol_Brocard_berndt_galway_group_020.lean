-- Prove2me | solution 1 for Brocard.berndt_galway_group_020
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:22:28.437112+00:00
-- url     : https://prove2.me/submissions/d9526334-ca0b-4651-9755-e4355c78642c

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0883
import Theorems.Thm_Brocard_berndt_galway_chunk_0884
import Theorems.Thm_Brocard_berndt_galway_chunk_0885
import Theorems.Thm_Brocard_berndt_galway_chunk_0886
import Theorems.Thm_Brocard_berndt_galway_chunk_0887
import Theorems.Thm_Brocard_berndt_galway_chunk_0888
import Theorems.Thm_Brocard_berndt_galway_chunk_0889
import Theorems.Thm_Brocard_berndt_galway_chunk_0890
import Theorems.Thm_Brocard_berndt_galway_chunk_0891
import Theorems.Thm_Brocard_berndt_galway_chunk_0892
import Theorems.Thm_Brocard_berndt_galway_chunk_0893
import Theorems.Thm_Brocard_berndt_galway_chunk_0894
import Theorems.Thm_Brocard_berndt_galway_chunk_0895
import Theorems.Thm_Brocard_berndt_galway_chunk_0896
import Theorems.Thm_Brocard_berndt_galway_chunk_0897
import Theorems.Thm_Brocard_berndt_galway_chunk_0898
import Theorems.Thm_Brocard_berndt_galway_chunk_0899
import Theorems.Thm_Brocard_berndt_galway_chunk_0900
import Theorems.Thm_Brocard_berndt_galway_chunk_0901
import Theorems.Thm_Brocard_berndt_galway_chunk_0902
import Theorems.Thm_Brocard_berndt_galway_chunk_0903
import Theorems.Thm_Brocard_berndt_galway_chunk_0904
import Theorems.Thm_Brocard_berndt_galway_chunk_0905
import Theorems.Thm_Brocard_berndt_galway_chunk_0906
import Theorems.Thm_Brocard_berndt_galway_chunk_0907
import Theorems.Thm_Brocard_berndt_galway_chunk_0908
import Theorems.Thm_Brocard_berndt_galway_chunk_0909
import Theorems.Thm_Brocard_berndt_galway_chunk_0910
import Theorems.Thm_Brocard_berndt_galway_chunk_0911
import Theorems.Thm_Brocard_berndt_galway_chunk_0912
import Theorems.Thm_Brocard_berndt_galway_chunk_0913
import Theorems.Thm_Brocard_berndt_galway_chunk_0914
import Theorems.Thm_Brocard_berndt_galway_chunk_0915
import Theorems.Thm_Brocard_berndt_galway_chunk_0916
import Theorems.Thm_Brocard_berndt_galway_chunk_0917
import Theorems.Thm_Brocard_berndt_galway_chunk_0918
import Theorems.Thm_Brocard_berndt_galway_chunk_0919
import Theorems.Thm_Brocard_berndt_galway_chunk_0920
import Theorems.Thm_Brocard_berndt_galway_chunk_0921
import Theorems.Thm_Brocard_berndt_galway_chunk_0922
import Theorems.Thm_Brocard_berndt_galway_chunk_0923
import Theorems.Thm_Brocard_berndt_galway_chunk_0924
import Theorems.Thm_Brocard_berndt_galway_chunk_0925
import Theorems.Thm_Brocard_berndt_galway_chunk_0926
import Theorems.Thm_Brocard_berndt_galway_chunk_0927
import Theorems.Thm_Brocard_berndt_galway_chunk_0928

theorem solution (n m : ℕ) (h1 : 158633093 ≤ n) (h2 : n < 166906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 162769784 with hs0 | hs0
  · -- n < 162769784
    rcases Nat.lt_or_ge n 160791366 with hs1 | hs1
    · -- n < 160791366
      rcases Nat.lt_or_ge n 159712230 with hs2 | hs2
      · -- n < 159712230
        rcases Nat.lt_or_ge n 159172661 with hs3 | hs3
        · -- n < 159172661
          rcases Nat.lt_or_ge n 158992805 with hs4 | hs4
          · -- n < 158992805
            rcases Nat.lt_or_ge n 158812949 with hs5 | hs5
            · -- n < 158812949
              exact Brocard.berndt_galway_chunk_0883 n m (by omega) (by omega) h
            · -- n >= 158812949
              exact Brocard.berndt_galway_chunk_0884 n m (by omega) (by omega) h
          · -- n >= 158992805
            exact Brocard.berndt_galway_chunk_0885 n m (by omega) (by omega) h
        · -- n >= 159172661
          rcases Nat.lt_or_ge n 159532374 with hs4 | hs4
          · -- n < 159532374
            rcases Nat.lt_or_ge n 159352517 with hs5 | hs5
            · -- n < 159352517
              exact Brocard.berndt_galway_chunk_0886 n m (by omega) (by omega) h
            · -- n >= 159352517
              exact Brocard.berndt_galway_chunk_0887 n m (by omega) (by omega) h
          · -- n >= 159532374
            exact Brocard.berndt_galway_chunk_0888 n m (by omega) (by omega) h
      · -- n >= 159712230
        rcases Nat.lt_or_ge n 160251798 with hs3 | hs3
        · -- n < 160251798
          rcases Nat.lt_or_ge n 160071942 with hs4 | hs4
          · -- n < 160071942
            rcases Nat.lt_or_ge n 159892086 with hs5 | hs5
            · -- n < 159892086
              exact Brocard.berndt_galway_chunk_0889 n m (by omega) (by omega) h
            · -- n >= 159892086
              exact Brocard.berndt_galway_chunk_0890 n m (by omega) (by omega) h
          · -- n >= 160071942
            exact Brocard.berndt_galway_chunk_0891 n m (by omega) (by omega) h
        · -- n >= 160251798
          rcases Nat.lt_or_ge n 160611510 with hs4 | hs4
          · -- n < 160611510
            rcases Nat.lt_or_ge n 160431654 with hs5 | hs5
            · -- n < 160431654
              exact Brocard.berndt_galway_chunk_0892 n m (by omega) (by omega) h
            · -- n >= 160431654
              exact Brocard.berndt_galway_chunk_0893 n m (by omega) (by omega) h
          · -- n >= 160611510
            exact Brocard.berndt_galway_chunk_0894 n m (by omega) (by omega) h
    · -- n >= 160791366
      rcases Nat.lt_or_ge n 161870503 with hs2 | hs2
      · -- n < 161870503
        rcases Nat.lt_or_ge n 161330935 with hs3 | hs3
        · -- n < 161330935
          rcases Nat.lt_or_ge n 161151079 with hs4 | hs4
          · -- n < 161151079
            rcases Nat.lt_or_ge n 160971223 with hs5 | hs5
            · -- n < 160971223
              exact Brocard.berndt_galway_chunk_0895 n m (by omega) (by omega) h
            · -- n >= 160971223
              exact Brocard.berndt_galway_chunk_0896 n m (by omega) (by omega) h
          · -- n >= 161151079
            exact Brocard.berndt_galway_chunk_0897 n m (by omega) (by omega) h
        · -- n >= 161330935
          rcases Nat.lt_or_ge n 161690647 with hs4 | hs4
          · -- n < 161690647
            rcases Nat.lt_or_ge n 161510791 with hs5 | hs5
            · -- n < 161510791
              exact Brocard.berndt_galway_chunk_0898 n m (by omega) (by omega) h
            · -- n >= 161510791
              exact Brocard.berndt_galway_chunk_0899 n m (by omega) (by omega) h
          · -- n >= 161690647
            exact Brocard.berndt_galway_chunk_0900 n m (by omega) (by omega) h
      · -- n >= 161870503
        rcases Nat.lt_or_ge n 162410071 with hs3 | hs3
        · -- n < 162410071
          rcases Nat.lt_or_ge n 162230215 with hs4 | hs4
          · -- n < 162230215
            rcases Nat.lt_or_ge n 162050359 with hs5 | hs5
            · -- n < 162050359
              exact Brocard.berndt_galway_chunk_0901 n m (by omega) (by omega) h
            · -- n >= 162050359
              exact Brocard.berndt_galway_chunk_0902 n m (by omega) (by omega) h
          · -- n >= 162230215
            exact Brocard.berndt_galway_chunk_0903 n m (by omega) (by omega) h
        · -- n >= 162410071
          rcases Nat.lt_or_ge n 162589928 with hs4 | hs4
          · -- n < 162589928
            exact Brocard.berndt_galway_chunk_0904 n m (by omega) (by omega) h
          · -- n >= 162589928
            exact Brocard.berndt_galway_chunk_0905 n m (by omega) (by omega) h
  · -- n >= 162769784
    rcases Nat.lt_or_ge n 164928057 with hs1 | hs1
    · -- n < 164928057
      rcases Nat.lt_or_ge n 163848920 with hs2 | hs2
      · -- n < 163848920
        rcases Nat.lt_or_ge n 163309352 with hs3 | hs3
        · -- n < 163309352
          rcases Nat.lt_or_ge n 163129496 with hs4 | hs4
          · -- n < 163129496
            rcases Nat.lt_or_ge n 162949640 with hs5 | hs5
            · -- n < 162949640
              exact Brocard.berndt_galway_chunk_0906 n m (by omega) (by omega) h
            · -- n >= 162949640
              exact Brocard.berndt_galway_chunk_0907 n m (by omega) (by omega) h
          · -- n >= 163129496
            exact Brocard.berndt_galway_chunk_0908 n m (by omega) (by omega) h
        · -- n >= 163309352
          rcases Nat.lt_or_ge n 163669064 with hs4 | hs4
          · -- n < 163669064
            rcases Nat.lt_or_ge n 163489208 with hs5 | hs5
            · -- n < 163489208
              exact Brocard.berndt_galway_chunk_0909 n m (by omega) (by omega) h
            · -- n >= 163489208
              exact Brocard.berndt_galway_chunk_0910 n m (by omega) (by omega) h
          · -- n >= 163669064
            exact Brocard.berndt_galway_chunk_0911 n m (by omega) (by omega) h
      · -- n >= 163848920
        rcases Nat.lt_or_ge n 164388489 with hs3 | hs3
        · -- n < 164388489
          rcases Nat.lt_or_ge n 164208633 with hs4 | hs4
          · -- n < 164208633
            rcases Nat.lt_or_ge n 164028776 with hs5 | hs5
            · -- n < 164028776
              exact Brocard.berndt_galway_chunk_0912 n m (by omega) (by omega) h
            · -- n >= 164028776
              exact Brocard.berndt_galway_chunk_0913 n m (by omega) (by omega) h
          · -- n >= 164208633
            exact Brocard.berndt_galway_chunk_0914 n m (by omega) (by omega) h
        · -- n >= 164388489
          rcases Nat.lt_or_ge n 164748201 with hs4 | hs4
          · -- n < 164748201
            rcases Nat.lt_or_ge n 164568345 with hs5 | hs5
            · -- n < 164568345
              exact Brocard.berndt_galway_chunk_0915 n m (by omega) (by omega) h
            · -- n >= 164568345
              exact Brocard.berndt_galway_chunk_0916 n m (by omega) (by omega) h
          · -- n >= 164748201
            exact Brocard.berndt_galway_chunk_0917 n m (by omega) (by omega) h
    · -- n >= 164928057
      rcases Nat.lt_or_ge n 166007194 with hs2 | hs2
      · -- n < 166007194
        rcases Nat.lt_or_ge n 165467625 with hs3 | hs3
        · -- n < 165467625
          rcases Nat.lt_or_ge n 165287769 with hs4 | hs4
          · -- n < 165287769
            rcases Nat.lt_or_ge n 165107913 with hs5 | hs5
            · -- n < 165107913
              exact Brocard.berndt_galway_chunk_0918 n m (by omega) (by omega) h
            · -- n >= 165107913
              exact Brocard.berndt_galway_chunk_0919 n m (by omega) (by omega) h
          · -- n >= 165287769
            exact Brocard.berndt_galway_chunk_0920 n m (by omega) (by omega) h
        · -- n >= 165467625
          rcases Nat.lt_or_ge n 165827338 with hs4 | hs4
          · -- n < 165827338
            rcases Nat.lt_or_ge n 165647482 with hs5 | hs5
            · -- n < 165647482
              exact Brocard.berndt_galway_chunk_0921 n m (by omega) (by omega) h
            · -- n >= 165647482
              exact Brocard.berndt_galway_chunk_0922 n m (by omega) (by omega) h
          · -- n >= 165827338
            exact Brocard.berndt_galway_chunk_0923 n m (by omega) (by omega) h
      · -- n >= 166007194
        rcases Nat.lt_or_ge n 166546762 with hs3 | hs3
        · -- n < 166546762
          rcases Nat.lt_or_ge n 166366906 with hs4 | hs4
          · -- n < 166366906
            rcases Nat.lt_or_ge n 166187050 with hs5 | hs5
            · -- n < 166187050
              exact Brocard.berndt_galway_chunk_0924 n m (by omega) (by omega) h
            · -- n >= 166187050
              exact Brocard.berndt_galway_chunk_0925 n m (by omega) (by omega) h
          · -- n >= 166366906
            exact Brocard.berndt_galway_chunk_0926 n m (by omega) (by omega) h
        · -- n >= 166546762
          rcases Nat.lt_or_ge n 166726618 with hs4 | hs4
          · -- n < 166726618
            exact Brocard.berndt_galway_chunk_0927 n m (by omega) (by omega) h
          · -- n >= 166726618
            exact Brocard.berndt_galway_chunk_0928 n m (by omega) (by omega) h

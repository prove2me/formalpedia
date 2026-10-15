-- Prove2me | solution 1 for Brocard.berndt_galway_group_107
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:27:05.713189+00:00
-- url     : https://prove2.me/submissions/2188747b-f106-42a1-b302-85c61076dcb4

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4913
import Theorems.Thm_Brocard_berndt_galway_chunk_4914
import Theorems.Thm_Brocard_berndt_galway_chunk_4915
import Theorems.Thm_Brocard_berndt_galway_chunk_4916
import Theorems.Thm_Brocard_berndt_galway_chunk_4917
import Theorems.Thm_Brocard_berndt_galway_chunk_4918
import Theorems.Thm_Brocard_berndt_galway_chunk_4919
import Theorems.Thm_Brocard_berndt_galway_chunk_4920
import Theorems.Thm_Brocard_berndt_galway_chunk_4921
import Theorems.Thm_Brocard_berndt_galway_chunk_4922
import Theorems.Thm_Brocard_berndt_galway_chunk_4923
import Theorems.Thm_Brocard_berndt_galway_chunk_4924
import Theorems.Thm_Brocard_berndt_galway_chunk_4925
import Theorems.Thm_Brocard_berndt_galway_chunk_4926
import Theorems.Thm_Brocard_berndt_galway_chunk_4927
import Theorems.Thm_Brocard_berndt_galway_chunk_4928
import Theorems.Thm_Brocard_berndt_galway_chunk_4929
import Theorems.Thm_Brocard_berndt_galway_chunk_4930
import Theorems.Thm_Brocard_berndt_galway_chunk_4931
import Theorems.Thm_Brocard_berndt_galway_chunk_4932
import Theorems.Thm_Brocard_berndt_galway_chunk_4933
import Theorems.Thm_Brocard_berndt_galway_chunk_4934
import Theorems.Thm_Brocard_berndt_galway_chunk_4935
import Theorems.Thm_Brocard_berndt_galway_chunk_4936
import Theorems.Thm_Brocard_berndt_galway_chunk_4937
import Theorems.Thm_Brocard_berndt_galway_chunk_4938
import Theorems.Thm_Brocard_berndt_galway_chunk_4939
import Theorems.Thm_Brocard_berndt_galway_chunk_4940
import Theorems.Thm_Brocard_berndt_galway_chunk_4941
import Theorems.Thm_Brocard_berndt_galway_chunk_4942
import Theorems.Thm_Brocard_berndt_galway_chunk_4943
import Theorems.Thm_Brocard_berndt_galway_chunk_4944
import Theorems.Thm_Brocard_berndt_galway_chunk_4945
import Theorems.Thm_Brocard_berndt_galway_chunk_4946
import Theorems.Thm_Brocard_berndt_galway_chunk_4947
import Theorems.Thm_Brocard_berndt_galway_chunk_4948
import Theorems.Thm_Brocard_berndt_galway_chunk_4949
import Theorems.Thm_Brocard_berndt_galway_chunk_4950
import Theorems.Thm_Brocard_berndt_galway_chunk_4951
import Theorems.Thm_Brocard_berndt_galway_chunk_4952
import Theorems.Thm_Brocard_berndt_galway_chunk_4953
import Theorems.Thm_Brocard_berndt_galway_chunk_4954
import Theorems.Thm_Brocard_berndt_galway_chunk_4955
import Theorems.Thm_Brocard_berndt_galway_chunk_4956
import Theorems.Thm_Brocard_berndt_galway_chunk_4957
import Theorems.Thm_Brocard_berndt_galway_chunk_4958

theorem solution (n m : ℕ) (h1 : 883453237 ≤ n) (h2 : n < 891726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 887589928 with hs0 | hs0
  · -- n < 887589928
    rcases Nat.lt_or_ge n 885611510 with hs1 | hs1
    · -- n < 885611510
      rcases Nat.lt_or_ge n 884532374 with hs2 | hs2
      · -- n < 884532374
        rcases Nat.lt_or_ge n 883992805 with hs3 | hs3
        · -- n < 883992805
          rcases Nat.lt_or_ge n 883812949 with hs4 | hs4
          · -- n < 883812949
            rcases Nat.lt_or_ge n 883633093 with hs5 | hs5
            · -- n < 883633093
              exact Brocard.berndt_galway_chunk_4913 n m (by omega) (by omega) h
            · -- n >= 883633093
              exact Brocard.berndt_galway_chunk_4914 n m (by omega) (by omega) h
          · -- n >= 883812949
            exact Brocard.berndt_galway_chunk_4915 n m (by omega) (by omega) h
        · -- n >= 883992805
          rcases Nat.lt_or_ge n 884352517 with hs4 | hs4
          · -- n < 884352517
            rcases Nat.lt_or_ge n 884172661 with hs5 | hs5
            · -- n < 884172661
              exact Brocard.berndt_galway_chunk_4916 n m (by omega) (by omega) h
            · -- n >= 884172661
              exact Brocard.berndt_galway_chunk_4917 n m (by omega) (by omega) h
          · -- n >= 884352517
            exact Brocard.berndt_galway_chunk_4918 n m (by omega) (by omega) h
      · -- n >= 884532374
        rcases Nat.lt_or_ge n 885071942 with hs3 | hs3
        · -- n < 885071942
          rcases Nat.lt_or_ge n 884892086 with hs4 | hs4
          · -- n < 884892086
            rcases Nat.lt_or_ge n 884712230 with hs5 | hs5
            · -- n < 884712230
              exact Brocard.berndt_galway_chunk_4919 n m (by omega) (by omega) h
            · -- n >= 884712230
              exact Brocard.berndt_galway_chunk_4920 n m (by omega) (by omega) h
          · -- n >= 884892086
            exact Brocard.berndt_galway_chunk_4921 n m (by omega) (by omega) h
        · -- n >= 885071942
          rcases Nat.lt_or_ge n 885431654 with hs4 | hs4
          · -- n < 885431654
            rcases Nat.lt_or_ge n 885251798 with hs5 | hs5
            · -- n < 885251798
              exact Brocard.berndt_galway_chunk_4922 n m (by omega) (by omega) h
            · -- n >= 885251798
              exact Brocard.berndt_galway_chunk_4923 n m (by omega) (by omega) h
          · -- n >= 885431654
            exact Brocard.berndt_galway_chunk_4924 n m (by omega) (by omega) h
    · -- n >= 885611510
      rcases Nat.lt_or_ge n 886690647 with hs2 | hs2
      · -- n < 886690647
        rcases Nat.lt_or_ge n 886151079 with hs3 | hs3
        · -- n < 886151079
          rcases Nat.lt_or_ge n 885971223 with hs4 | hs4
          · -- n < 885971223
            rcases Nat.lt_or_ge n 885791366 with hs5 | hs5
            · -- n < 885791366
              exact Brocard.berndt_galway_chunk_4925 n m (by omega) (by omega) h
            · -- n >= 885791366
              exact Brocard.berndt_galway_chunk_4926 n m (by omega) (by omega) h
          · -- n >= 885971223
            exact Brocard.berndt_galway_chunk_4927 n m (by omega) (by omega) h
        · -- n >= 886151079
          rcases Nat.lt_or_ge n 886510791 with hs4 | hs4
          · -- n < 886510791
            rcases Nat.lt_or_ge n 886330935 with hs5 | hs5
            · -- n < 886330935
              exact Brocard.berndt_galway_chunk_4928 n m (by omega) (by omega) h
            · -- n >= 886330935
              exact Brocard.berndt_galway_chunk_4929 n m (by omega) (by omega) h
          · -- n >= 886510791
            exact Brocard.berndt_galway_chunk_4930 n m (by omega) (by omega) h
      · -- n >= 886690647
        rcases Nat.lt_or_ge n 887230215 with hs3 | hs3
        · -- n < 887230215
          rcases Nat.lt_or_ge n 887050359 with hs4 | hs4
          · -- n < 887050359
            rcases Nat.lt_or_ge n 886870503 with hs5 | hs5
            · -- n < 886870503
              exact Brocard.berndt_galway_chunk_4931 n m (by omega) (by omega) h
            · -- n >= 886870503
              exact Brocard.berndt_galway_chunk_4932 n m (by omega) (by omega) h
          · -- n >= 887050359
            exact Brocard.berndt_galway_chunk_4933 n m (by omega) (by omega) h
        · -- n >= 887230215
          rcases Nat.lt_or_ge n 887410071 with hs4 | hs4
          · -- n < 887410071
            exact Brocard.berndt_galway_chunk_4934 n m (by omega) (by omega) h
          · -- n >= 887410071
            exact Brocard.berndt_galway_chunk_4935 n m (by omega) (by omega) h
  · -- n >= 887589928
    rcases Nat.lt_or_ge n 889748201 with hs1 | hs1
    · -- n < 889748201
      rcases Nat.lt_or_ge n 888669064 with hs2 | hs2
      · -- n < 888669064
        rcases Nat.lt_or_ge n 888129496 with hs3 | hs3
        · -- n < 888129496
          rcases Nat.lt_or_ge n 887949640 with hs4 | hs4
          · -- n < 887949640
            rcases Nat.lt_or_ge n 887769784 with hs5 | hs5
            · -- n < 887769784
              exact Brocard.berndt_galway_chunk_4936 n m (by omega) (by omega) h
            · -- n >= 887769784
              exact Brocard.berndt_galway_chunk_4937 n m (by omega) (by omega) h
          · -- n >= 887949640
            exact Brocard.berndt_galway_chunk_4938 n m (by omega) (by omega) h
        · -- n >= 888129496
          rcases Nat.lt_or_ge n 888489208 with hs4 | hs4
          · -- n < 888489208
            rcases Nat.lt_or_ge n 888309352 with hs5 | hs5
            · -- n < 888309352
              exact Brocard.berndt_galway_chunk_4939 n m (by omega) (by omega) h
            · -- n >= 888309352
              exact Brocard.berndt_galway_chunk_4940 n m (by omega) (by omega) h
          · -- n >= 888489208
            exact Brocard.berndt_galway_chunk_4941 n m (by omega) (by omega) h
      · -- n >= 888669064
        rcases Nat.lt_or_ge n 889208633 with hs3 | hs3
        · -- n < 889208633
          rcases Nat.lt_or_ge n 889028776 with hs4 | hs4
          · -- n < 889028776
            rcases Nat.lt_or_ge n 888848920 with hs5 | hs5
            · -- n < 888848920
              exact Brocard.berndt_galway_chunk_4942 n m (by omega) (by omega) h
            · -- n >= 888848920
              exact Brocard.berndt_galway_chunk_4943 n m (by omega) (by omega) h
          · -- n >= 889028776
            exact Brocard.berndt_galway_chunk_4944 n m (by omega) (by omega) h
        · -- n >= 889208633
          rcases Nat.lt_or_ge n 889568345 with hs4 | hs4
          · -- n < 889568345
            rcases Nat.lt_or_ge n 889388489 with hs5 | hs5
            · -- n < 889388489
              exact Brocard.berndt_galway_chunk_4945 n m (by omega) (by omega) h
            · -- n >= 889388489
              exact Brocard.berndt_galway_chunk_4946 n m (by omega) (by omega) h
          · -- n >= 889568345
            exact Brocard.berndt_galway_chunk_4947 n m (by omega) (by omega) h
    · -- n >= 889748201
      rcases Nat.lt_or_ge n 890827338 with hs2 | hs2
      · -- n < 890827338
        rcases Nat.lt_or_ge n 890287769 with hs3 | hs3
        · -- n < 890287769
          rcases Nat.lt_or_ge n 890107913 with hs4 | hs4
          · -- n < 890107913
            rcases Nat.lt_or_ge n 889928057 with hs5 | hs5
            · -- n < 889928057
              exact Brocard.berndt_galway_chunk_4948 n m (by omega) (by omega) h
            · -- n >= 889928057
              exact Brocard.berndt_galway_chunk_4949 n m (by omega) (by omega) h
          · -- n >= 890107913
            exact Brocard.berndt_galway_chunk_4950 n m (by omega) (by omega) h
        · -- n >= 890287769
          rcases Nat.lt_or_ge n 890647482 with hs4 | hs4
          · -- n < 890647482
            rcases Nat.lt_or_ge n 890467625 with hs5 | hs5
            · -- n < 890467625
              exact Brocard.berndt_galway_chunk_4951 n m (by omega) (by omega) h
            · -- n >= 890467625
              exact Brocard.berndt_galway_chunk_4952 n m (by omega) (by omega) h
          · -- n >= 890647482
            exact Brocard.berndt_galway_chunk_4953 n m (by omega) (by omega) h
      · -- n >= 890827338
        rcases Nat.lt_or_ge n 891366906 with hs3 | hs3
        · -- n < 891366906
          rcases Nat.lt_or_ge n 891187050 with hs4 | hs4
          · -- n < 891187050
            rcases Nat.lt_or_ge n 891007194 with hs5 | hs5
            · -- n < 891007194
              exact Brocard.berndt_galway_chunk_4954 n m (by omega) (by omega) h
            · -- n >= 891007194
              exact Brocard.berndt_galway_chunk_4955 n m (by omega) (by omega) h
          · -- n >= 891187050
            exact Brocard.berndt_galway_chunk_4956 n m (by omega) (by omega) h
        · -- n >= 891366906
          rcases Nat.lt_or_ge n 891546762 with hs4 | hs4
          · -- n < 891546762
            exact Brocard.berndt_galway_chunk_4957 n m (by omega) (by omega) h
          · -- n >= 891546762
            exact Brocard.berndt_galway_chunk_4958 n m (by omega) (by omega) h

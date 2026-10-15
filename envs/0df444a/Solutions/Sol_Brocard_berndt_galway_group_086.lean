-- Prove2me | solution 1 for Brocard.berndt_galway_group_086
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:23:17.415057+00:00
-- url     : https://prove2.me/submissions/6719f077-4557-440b-adc4-774c97382144

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3940
import Theorems.Thm_Brocard_berndt_galway_chunk_3941
import Theorems.Thm_Brocard_berndt_galway_chunk_3942
import Theorems.Thm_Brocard_berndt_galway_chunk_3943
import Theorems.Thm_Brocard_berndt_galway_chunk_3944
import Theorems.Thm_Brocard_berndt_galway_chunk_3945
import Theorems.Thm_Brocard_berndt_galway_chunk_3946
import Theorems.Thm_Brocard_berndt_galway_chunk_3947
import Theorems.Thm_Brocard_berndt_galway_chunk_3948
import Theorems.Thm_Brocard_berndt_galway_chunk_3949
import Theorems.Thm_Brocard_berndt_galway_chunk_3950
import Theorems.Thm_Brocard_berndt_galway_chunk_3951
import Theorems.Thm_Brocard_berndt_galway_chunk_3952
import Theorems.Thm_Brocard_berndt_galway_chunk_3953
import Theorems.Thm_Brocard_berndt_galway_chunk_3954
import Theorems.Thm_Brocard_berndt_galway_chunk_3955
import Theorems.Thm_Brocard_berndt_galway_chunk_3956
import Theorems.Thm_Brocard_berndt_galway_chunk_3957
import Theorems.Thm_Brocard_berndt_galway_chunk_3958
import Theorems.Thm_Brocard_berndt_galway_chunk_3959
import Theorems.Thm_Brocard_berndt_galway_chunk_3960
import Theorems.Thm_Brocard_berndt_galway_chunk_3961
import Theorems.Thm_Brocard_berndt_galway_chunk_3962
import Theorems.Thm_Brocard_berndt_galway_chunk_3963
import Theorems.Thm_Brocard_berndt_galway_chunk_3964
import Theorems.Thm_Brocard_berndt_galway_chunk_3965
import Theorems.Thm_Brocard_berndt_galway_chunk_3966
import Theorems.Thm_Brocard_berndt_galway_chunk_3967
import Theorems.Thm_Brocard_berndt_galway_chunk_3968
import Theorems.Thm_Brocard_berndt_galway_chunk_3969
import Theorems.Thm_Brocard_berndt_galway_chunk_3970
import Theorems.Thm_Brocard_berndt_galway_chunk_3971
import Theorems.Thm_Brocard_berndt_galway_chunk_3972
import Theorems.Thm_Brocard_berndt_galway_chunk_3973
import Theorems.Thm_Brocard_berndt_galway_chunk_3974
import Theorems.Thm_Brocard_berndt_galway_chunk_3975
import Theorems.Thm_Brocard_berndt_galway_chunk_3976
import Theorems.Thm_Brocard_berndt_galway_chunk_3977
import Theorems.Thm_Brocard_berndt_galway_chunk_3978
import Theorems.Thm_Brocard_berndt_galway_chunk_3979
import Theorems.Thm_Brocard_berndt_galway_chunk_3980
import Theorems.Thm_Brocard_berndt_galway_chunk_3981
import Theorems.Thm_Brocard_berndt_galway_chunk_3982
import Theorems.Thm_Brocard_berndt_galway_chunk_3983
import Theorems.Thm_Brocard_berndt_galway_chunk_3984
import Theorems.Thm_Brocard_berndt_galway_chunk_3985
import Theorems.Thm_Brocard_berndt_galway_chunk_3986

theorem solution (n m : ℕ) (h1 : 708453237 ≤ n) (h2 : n < 716906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 712769784 with hs0 | hs0
  · -- n < 712769784
    rcases Nat.lt_or_ge n 710611510 with hs1 | hs1
    · -- n < 710611510
      rcases Nat.lt_or_ge n 709532374 with hs2 | hs2
      · -- n < 709532374
        rcases Nat.lt_or_ge n 708992805 with hs3 | hs3
        · -- n < 708992805
          rcases Nat.lt_or_ge n 708812949 with hs4 | hs4
          · -- n < 708812949
            rcases Nat.lt_or_ge n 708633093 with hs5 | hs5
            · -- n < 708633093
              exact Brocard.berndt_galway_chunk_3940 n m (by omega) (by omega) h
            · -- n >= 708633093
              exact Brocard.berndt_galway_chunk_3941 n m (by omega) (by omega) h
          · -- n >= 708812949
            exact Brocard.berndt_galway_chunk_3942 n m (by omega) (by omega) h
        · -- n >= 708992805
          rcases Nat.lt_or_ge n 709352517 with hs4 | hs4
          · -- n < 709352517
            rcases Nat.lt_or_ge n 709172661 with hs5 | hs5
            · -- n < 709172661
              exact Brocard.berndt_galway_chunk_3943 n m (by omega) (by omega) h
            · -- n >= 709172661
              exact Brocard.berndt_galway_chunk_3944 n m (by omega) (by omega) h
          · -- n >= 709352517
            exact Brocard.berndt_galway_chunk_3945 n m (by omega) (by omega) h
      · -- n >= 709532374
        rcases Nat.lt_or_ge n 710071942 with hs3 | hs3
        · -- n < 710071942
          rcases Nat.lt_or_ge n 709892086 with hs4 | hs4
          · -- n < 709892086
            rcases Nat.lt_or_ge n 709712230 with hs5 | hs5
            · -- n < 709712230
              exact Brocard.berndt_galway_chunk_3946 n m (by omega) (by omega) h
            · -- n >= 709712230
              exact Brocard.berndt_galway_chunk_3947 n m (by omega) (by omega) h
          · -- n >= 709892086
            exact Brocard.berndt_galway_chunk_3948 n m (by omega) (by omega) h
        · -- n >= 710071942
          rcases Nat.lt_or_ge n 710431654 with hs4 | hs4
          · -- n < 710431654
            rcases Nat.lt_or_ge n 710251798 with hs5 | hs5
            · -- n < 710251798
              exact Brocard.berndt_galway_chunk_3949 n m (by omega) (by omega) h
            · -- n >= 710251798
              exact Brocard.berndt_galway_chunk_3950 n m (by omega) (by omega) h
          · -- n >= 710431654
            exact Brocard.berndt_galway_chunk_3951 n m (by omega) (by omega) h
    · -- n >= 710611510
      rcases Nat.lt_or_ge n 711690647 with hs2 | hs2
      · -- n < 711690647
        rcases Nat.lt_or_ge n 711151079 with hs3 | hs3
        · -- n < 711151079
          rcases Nat.lt_or_ge n 710971223 with hs4 | hs4
          · -- n < 710971223
            rcases Nat.lt_or_ge n 710791366 with hs5 | hs5
            · -- n < 710791366
              exact Brocard.berndt_galway_chunk_3952 n m (by omega) (by omega) h
            · -- n >= 710791366
              exact Brocard.berndt_galway_chunk_3953 n m (by omega) (by omega) h
          · -- n >= 710971223
            exact Brocard.berndt_galway_chunk_3954 n m (by omega) (by omega) h
        · -- n >= 711151079
          rcases Nat.lt_or_ge n 711510791 with hs4 | hs4
          · -- n < 711510791
            rcases Nat.lt_or_ge n 711330935 with hs5 | hs5
            · -- n < 711330935
              exact Brocard.berndt_galway_chunk_3955 n m (by omega) (by omega) h
            · -- n >= 711330935
              exact Brocard.berndt_galway_chunk_3956 n m (by omega) (by omega) h
          · -- n >= 711510791
            exact Brocard.berndt_galway_chunk_3957 n m (by omega) (by omega) h
      · -- n >= 711690647
        rcases Nat.lt_or_ge n 712230215 with hs3 | hs3
        · -- n < 712230215
          rcases Nat.lt_or_ge n 712050359 with hs4 | hs4
          · -- n < 712050359
            rcases Nat.lt_or_ge n 711870503 with hs5 | hs5
            · -- n < 711870503
              exact Brocard.berndt_galway_chunk_3958 n m (by omega) (by omega) h
            · -- n >= 711870503
              exact Brocard.berndt_galway_chunk_3959 n m (by omega) (by omega) h
          · -- n >= 712050359
            exact Brocard.berndt_galway_chunk_3960 n m (by omega) (by omega) h
        · -- n >= 712230215
          rcases Nat.lt_or_ge n 712589928 with hs4 | hs4
          · -- n < 712589928
            rcases Nat.lt_or_ge n 712410071 with hs5 | hs5
            · -- n < 712410071
              exact Brocard.berndt_galway_chunk_3961 n m (by omega) (by omega) h
            · -- n >= 712410071
              exact Brocard.berndt_galway_chunk_3962 n m (by omega) (by omega) h
          · -- n >= 712589928
            exact Brocard.berndt_galway_chunk_3963 n m (by omega) (by omega) h
  · -- n >= 712769784
    rcases Nat.lt_or_ge n 714928057 with hs1 | hs1
    · -- n < 714928057
      rcases Nat.lt_or_ge n 713848920 with hs2 | hs2
      · -- n < 713848920
        rcases Nat.lt_or_ge n 713309352 with hs3 | hs3
        · -- n < 713309352
          rcases Nat.lt_or_ge n 713129496 with hs4 | hs4
          · -- n < 713129496
            rcases Nat.lt_or_ge n 712949640 with hs5 | hs5
            · -- n < 712949640
              exact Brocard.berndt_galway_chunk_3964 n m (by omega) (by omega) h
            · -- n >= 712949640
              exact Brocard.berndt_galway_chunk_3965 n m (by omega) (by omega) h
          · -- n >= 713129496
            exact Brocard.berndt_galway_chunk_3966 n m (by omega) (by omega) h
        · -- n >= 713309352
          rcases Nat.lt_or_ge n 713669064 with hs4 | hs4
          · -- n < 713669064
            rcases Nat.lt_or_ge n 713489208 with hs5 | hs5
            · -- n < 713489208
              exact Brocard.berndt_galway_chunk_3967 n m (by omega) (by omega) h
            · -- n >= 713489208
              exact Brocard.berndt_galway_chunk_3968 n m (by omega) (by omega) h
          · -- n >= 713669064
            exact Brocard.berndt_galway_chunk_3969 n m (by omega) (by omega) h
      · -- n >= 713848920
        rcases Nat.lt_or_ge n 714388489 with hs3 | hs3
        · -- n < 714388489
          rcases Nat.lt_or_ge n 714208633 with hs4 | hs4
          · -- n < 714208633
            rcases Nat.lt_or_ge n 714028776 with hs5 | hs5
            · -- n < 714028776
              exact Brocard.berndt_galway_chunk_3970 n m (by omega) (by omega) h
            · -- n >= 714028776
              exact Brocard.berndt_galway_chunk_3971 n m (by omega) (by omega) h
          · -- n >= 714208633
            exact Brocard.berndt_galway_chunk_3972 n m (by omega) (by omega) h
        · -- n >= 714388489
          rcases Nat.lt_or_ge n 714748201 with hs4 | hs4
          · -- n < 714748201
            rcases Nat.lt_or_ge n 714568345 with hs5 | hs5
            · -- n < 714568345
              exact Brocard.berndt_galway_chunk_3973 n m (by omega) (by omega) h
            · -- n >= 714568345
              exact Brocard.berndt_galway_chunk_3974 n m (by omega) (by omega) h
          · -- n >= 714748201
            exact Brocard.berndt_galway_chunk_3975 n m (by omega) (by omega) h
    · -- n >= 714928057
      rcases Nat.lt_or_ge n 716007194 with hs2 | hs2
      · -- n < 716007194
        rcases Nat.lt_or_ge n 715467625 with hs3 | hs3
        · -- n < 715467625
          rcases Nat.lt_or_ge n 715287769 with hs4 | hs4
          · -- n < 715287769
            rcases Nat.lt_or_ge n 715107913 with hs5 | hs5
            · -- n < 715107913
              exact Brocard.berndt_galway_chunk_3976 n m (by omega) (by omega) h
            · -- n >= 715107913
              exact Brocard.berndt_galway_chunk_3977 n m (by omega) (by omega) h
          · -- n >= 715287769
            exact Brocard.berndt_galway_chunk_3978 n m (by omega) (by omega) h
        · -- n >= 715467625
          rcases Nat.lt_or_ge n 715827338 with hs4 | hs4
          · -- n < 715827338
            rcases Nat.lt_or_ge n 715647482 with hs5 | hs5
            · -- n < 715647482
              exact Brocard.berndt_galway_chunk_3979 n m (by omega) (by omega) h
            · -- n >= 715647482
              exact Brocard.berndt_galway_chunk_3980 n m (by omega) (by omega) h
          · -- n >= 715827338
            exact Brocard.berndt_galway_chunk_3981 n m (by omega) (by omega) h
      · -- n >= 716007194
        rcases Nat.lt_or_ge n 716546762 with hs3 | hs3
        · -- n < 716546762
          rcases Nat.lt_or_ge n 716366906 with hs4 | hs4
          · -- n < 716366906
            rcases Nat.lt_or_ge n 716187050 with hs5 | hs5
            · -- n < 716187050
              exact Brocard.berndt_galway_chunk_3982 n m (by omega) (by omega) h
            · -- n >= 716187050
              exact Brocard.berndt_galway_chunk_3983 n m (by omega) (by omega) h
          · -- n >= 716366906
            exact Brocard.berndt_galway_chunk_3984 n m (by omega) (by omega) h
        · -- n >= 716546762
          rcases Nat.lt_or_ge n 716726618 with hs4 | hs4
          · -- n < 716726618
            exact Brocard.berndt_galway_chunk_3985 n m (by omega) (by omega) h
          · -- n >= 716726618
            exact Brocard.berndt_galway_chunk_3986 n m (by omega) (by omega) h

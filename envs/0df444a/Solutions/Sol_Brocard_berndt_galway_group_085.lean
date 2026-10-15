-- Prove2me | solution 1 for Brocard.berndt_galway_group_085
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:14:06.152994+00:00
-- url     : https://prove2.me/submissions/2c8d362e-44c0-4e29-9e60-07a8c17c21e0

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3893
import Theorems.Thm_Brocard_berndt_galway_chunk_3894
import Theorems.Thm_Brocard_berndt_galway_chunk_3895
import Theorems.Thm_Brocard_berndt_galway_chunk_3896
import Theorems.Thm_Brocard_berndt_galway_chunk_3897
import Theorems.Thm_Brocard_berndt_galway_chunk_3898
import Theorems.Thm_Brocard_berndt_galway_chunk_3899
import Theorems.Thm_Brocard_berndt_galway_chunk_3900
import Theorems.Thm_Brocard_berndt_galway_chunk_3901
import Theorems.Thm_Brocard_berndt_galway_chunk_3902
import Theorems.Thm_Brocard_berndt_galway_chunk_3903
import Theorems.Thm_Brocard_berndt_galway_chunk_3904
import Theorems.Thm_Brocard_berndt_galway_chunk_3905
import Theorems.Thm_Brocard_berndt_galway_chunk_3906
import Theorems.Thm_Brocard_berndt_galway_chunk_3907
import Theorems.Thm_Brocard_berndt_galway_chunk_3908
import Theorems.Thm_Brocard_berndt_galway_chunk_3909
import Theorems.Thm_Brocard_berndt_galway_chunk_3910
import Theorems.Thm_Brocard_berndt_galway_chunk_3911
import Theorems.Thm_Brocard_berndt_galway_chunk_3912
import Theorems.Thm_Brocard_berndt_galway_chunk_3913
import Theorems.Thm_Brocard_berndt_galway_chunk_3914
import Theorems.Thm_Brocard_berndt_galway_chunk_3915
import Theorems.Thm_Brocard_berndt_galway_chunk_3916
import Theorems.Thm_Brocard_berndt_galway_chunk_3917
import Theorems.Thm_Brocard_berndt_galway_chunk_3918
import Theorems.Thm_Brocard_berndt_galway_chunk_3919
import Theorems.Thm_Brocard_berndt_galway_chunk_3920
import Theorems.Thm_Brocard_berndt_galway_chunk_3921
import Theorems.Thm_Brocard_berndt_galway_chunk_3922
import Theorems.Thm_Brocard_berndt_galway_chunk_3923
import Theorems.Thm_Brocard_berndt_galway_chunk_3924
import Theorems.Thm_Brocard_berndt_galway_chunk_3925
import Theorems.Thm_Brocard_berndt_galway_chunk_3926
import Theorems.Thm_Brocard_berndt_galway_chunk_3927
import Theorems.Thm_Brocard_berndt_galway_chunk_3928
import Theorems.Thm_Brocard_berndt_galway_chunk_3929
import Theorems.Thm_Brocard_berndt_galway_chunk_3930
import Theorems.Thm_Brocard_berndt_galway_chunk_3931
import Theorems.Thm_Brocard_berndt_galway_chunk_3932
import Theorems.Thm_Brocard_berndt_galway_chunk_3933
import Theorems.Thm_Brocard_berndt_galway_chunk_3934
import Theorems.Thm_Brocard_berndt_galway_chunk_3935
import Theorems.Thm_Brocard_berndt_galway_chunk_3936
import Theorems.Thm_Brocard_berndt_galway_chunk_3937
import Theorems.Thm_Brocard_berndt_galway_chunk_3938
import Theorems.Thm_Brocard_berndt_galway_chunk_3939

theorem solution (n m : ℕ) (h1 : 700000000 ≤ n) (h2 : n < 708453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 704316546 with hs0 | hs0
  · -- n < 704316546
    rcases Nat.lt_or_ge n 702158273 with hs1 | hs1
    · -- n < 702158273
      rcases Nat.lt_or_ge n 701079136 with hs2 | hs2
      · -- n < 701079136
        rcases Nat.lt_or_ge n 700539568 with hs3 | hs3
        · -- n < 700539568
          rcases Nat.lt_or_ge n 700359712 with hs4 | hs4
          · -- n < 700359712
            rcases Nat.lt_or_ge n 700179856 with hs5 | hs5
            · -- n < 700179856
              exact Brocard.berndt_galway_chunk_3893 n m (by omega) (by omega) h
            · -- n >= 700179856
              exact Brocard.berndt_galway_chunk_3894 n m (by omega) (by omega) h
          · -- n >= 700359712
            exact Brocard.berndt_galway_chunk_3895 n m (by omega) (by omega) h
        · -- n >= 700539568
          rcases Nat.lt_or_ge n 700899280 with hs4 | hs4
          · -- n < 700899280
            rcases Nat.lt_or_ge n 700719424 with hs5 | hs5
            · -- n < 700719424
              exact Brocard.berndt_galway_chunk_3896 n m (by omega) (by omega) h
            · -- n >= 700719424
              exact Brocard.berndt_galway_chunk_3897 n m (by omega) (by omega) h
          · -- n >= 700899280
            exact Brocard.berndt_galway_chunk_3898 n m (by omega) (by omega) h
      · -- n >= 701079136
        rcases Nat.lt_or_ge n 701618705 with hs3 | hs3
        · -- n < 701618705
          rcases Nat.lt_or_ge n 701438848 with hs4 | hs4
          · -- n < 701438848
            rcases Nat.lt_or_ge n 701258992 with hs5 | hs5
            · -- n < 701258992
              exact Brocard.berndt_galway_chunk_3899 n m (by omega) (by omega) h
            · -- n >= 701258992
              exact Brocard.berndt_galway_chunk_3900 n m (by omega) (by omega) h
          · -- n >= 701438848
            exact Brocard.berndt_galway_chunk_3901 n m (by omega) (by omega) h
        · -- n >= 701618705
          rcases Nat.lt_or_ge n 701978417 with hs4 | hs4
          · -- n < 701978417
            rcases Nat.lt_or_ge n 701798561 with hs5 | hs5
            · -- n < 701798561
              exact Brocard.berndt_galway_chunk_3902 n m (by omega) (by omega) h
            · -- n >= 701798561
              exact Brocard.berndt_galway_chunk_3903 n m (by omega) (by omega) h
          · -- n >= 701978417
            exact Brocard.berndt_galway_chunk_3904 n m (by omega) (by omega) h
    · -- n >= 702158273
      rcases Nat.lt_or_ge n 703237410 with hs2 | hs2
      · -- n < 703237410
        rcases Nat.lt_or_ge n 702697841 with hs3 | hs3
        · -- n < 702697841
          rcases Nat.lt_or_ge n 702517985 with hs4 | hs4
          · -- n < 702517985
            rcases Nat.lt_or_ge n 702338129 with hs5 | hs5
            · -- n < 702338129
              exact Brocard.berndt_galway_chunk_3905 n m (by omega) (by omega) h
            · -- n >= 702338129
              exact Brocard.berndt_galway_chunk_3906 n m (by omega) (by omega) h
          · -- n >= 702517985
            exact Brocard.berndt_galway_chunk_3907 n m (by omega) (by omega) h
        · -- n >= 702697841
          rcases Nat.lt_or_ge n 703057553 with hs4 | hs4
          · -- n < 703057553
            rcases Nat.lt_or_ge n 702877697 with hs5 | hs5
            · -- n < 702877697
              exact Brocard.berndt_galway_chunk_3908 n m (by omega) (by omega) h
            · -- n >= 702877697
              exact Brocard.berndt_galway_chunk_3909 n m (by omega) (by omega) h
          · -- n >= 703057553
            exact Brocard.berndt_galway_chunk_3910 n m (by omega) (by omega) h
      · -- n >= 703237410
        rcases Nat.lt_or_ge n 703776978 with hs3 | hs3
        · -- n < 703776978
          rcases Nat.lt_or_ge n 703597122 with hs4 | hs4
          · -- n < 703597122
            rcases Nat.lt_or_ge n 703417266 with hs5 | hs5
            · -- n < 703417266
              exact Brocard.berndt_galway_chunk_3911 n m (by omega) (by omega) h
            · -- n >= 703417266
              exact Brocard.berndt_galway_chunk_3912 n m (by omega) (by omega) h
          · -- n >= 703597122
            exact Brocard.berndt_galway_chunk_3913 n m (by omega) (by omega) h
        · -- n >= 703776978
          rcases Nat.lt_or_ge n 704136690 with hs4 | hs4
          · -- n < 704136690
            rcases Nat.lt_or_ge n 703956834 with hs5 | hs5
            · -- n < 703956834
              exact Brocard.berndt_galway_chunk_3914 n m (by omega) (by omega) h
            · -- n >= 703956834
              exact Brocard.berndt_galway_chunk_3915 n m (by omega) (by omega) h
          · -- n >= 704136690
            exact Brocard.berndt_galway_chunk_3916 n m (by omega) (by omega) h
  · -- n >= 704316546
    rcases Nat.lt_or_ge n 706474820 with hs1 | hs1
    · -- n < 706474820
      rcases Nat.lt_or_ge n 705395683 with hs2 | hs2
      · -- n < 705395683
        rcases Nat.lt_or_ge n 704856115 with hs3 | hs3
        · -- n < 704856115
          rcases Nat.lt_or_ge n 704676258 with hs4 | hs4
          · -- n < 704676258
            rcases Nat.lt_or_ge n 704496402 with hs5 | hs5
            · -- n < 704496402
              exact Brocard.berndt_galway_chunk_3917 n m (by omega) (by omega) h
            · -- n >= 704496402
              exact Brocard.berndt_galway_chunk_3918 n m (by omega) (by omega) h
          · -- n >= 704676258
            exact Brocard.berndt_galway_chunk_3919 n m (by omega) (by omega) h
        · -- n >= 704856115
          rcases Nat.lt_or_ge n 705215827 with hs4 | hs4
          · -- n < 705215827
            rcases Nat.lt_or_ge n 705035971 with hs5 | hs5
            · -- n < 705035971
              exact Brocard.berndt_galway_chunk_3920 n m (by omega) (by omega) h
            · -- n >= 705035971
              exact Brocard.berndt_galway_chunk_3921 n m (by omega) (by omega) h
          · -- n >= 705215827
            exact Brocard.berndt_galway_chunk_3922 n m (by omega) (by omega) h
      · -- n >= 705395683
        rcases Nat.lt_or_ge n 705935251 with hs3 | hs3
        · -- n < 705935251
          rcases Nat.lt_or_ge n 705755395 with hs4 | hs4
          · -- n < 705755395
            rcases Nat.lt_or_ge n 705575539 with hs5 | hs5
            · -- n < 705575539
              exact Brocard.berndt_galway_chunk_3923 n m (by omega) (by omega) h
            · -- n >= 705575539
              exact Brocard.berndt_galway_chunk_3924 n m (by omega) (by omega) h
          · -- n >= 705755395
            exact Brocard.berndt_galway_chunk_3925 n m (by omega) (by omega) h
        · -- n >= 705935251
          rcases Nat.lt_or_ge n 706294964 with hs4 | hs4
          · -- n < 706294964
            rcases Nat.lt_or_ge n 706115107 with hs5 | hs5
            · -- n < 706115107
              exact Brocard.berndt_galway_chunk_3926 n m (by omega) (by omega) h
            · -- n >= 706115107
              exact Brocard.berndt_galway_chunk_3927 n m (by omega) (by omega) h
          · -- n >= 706294964
            exact Brocard.berndt_galway_chunk_3928 n m (by omega) (by omega) h
    · -- n >= 706474820
      rcases Nat.lt_or_ge n 707553956 with hs2 | hs2
      · -- n < 707553956
        rcases Nat.lt_or_ge n 707014388 with hs3 | hs3
        · -- n < 707014388
          rcases Nat.lt_or_ge n 706834532 with hs4 | hs4
          · -- n < 706834532
            rcases Nat.lt_or_ge n 706654676 with hs5 | hs5
            · -- n < 706654676
              exact Brocard.berndt_galway_chunk_3929 n m (by omega) (by omega) h
            · -- n >= 706654676
              exact Brocard.berndt_galway_chunk_3930 n m (by omega) (by omega) h
          · -- n >= 706834532
            exact Brocard.berndt_galway_chunk_3931 n m (by omega) (by omega) h
        · -- n >= 707014388
          rcases Nat.lt_or_ge n 707374100 with hs4 | hs4
          · -- n < 707374100
            rcases Nat.lt_or_ge n 707194244 with hs5 | hs5
            · -- n < 707194244
              exact Brocard.berndt_galway_chunk_3932 n m (by omega) (by omega) h
            · -- n >= 707194244
              exact Brocard.berndt_galway_chunk_3933 n m (by omega) (by omega) h
          · -- n >= 707374100
            exact Brocard.berndt_galway_chunk_3934 n m (by omega) (by omega) h
      · -- n >= 707553956
        rcases Nat.lt_or_ge n 708093525 with hs3 | hs3
        · -- n < 708093525
          rcases Nat.lt_or_ge n 707913669 with hs4 | hs4
          · -- n < 707913669
            rcases Nat.lt_or_ge n 707733812 with hs5 | hs5
            · -- n < 707733812
              exact Brocard.berndt_galway_chunk_3935 n m (by omega) (by omega) h
            · -- n >= 707733812
              exact Brocard.berndt_galway_chunk_3936 n m (by omega) (by omega) h
          · -- n >= 707913669
            exact Brocard.berndt_galway_chunk_3937 n m (by omega) (by omega) h
        · -- n >= 708093525
          rcases Nat.lt_or_ge n 708273381 with hs4 | hs4
          · -- n < 708273381
            exact Brocard.berndt_galway_chunk_3938 n m (by omega) (by omega) h
          · -- n >= 708273381
            exact Brocard.berndt_galway_chunk_3939 n m (by omega) (by omega) h

-- Prove2me | solution 1 for Brocard.berndt_galway_group_042
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:23:15.993407+00:00
-- url     : https://prove2.me/submissions/6ba4f49f-7ad9-4a85-9ab8-1fa5772bee82

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1903
import Theorems.Thm_Brocard_berndt_galway_chunk_1904
import Theorems.Thm_Brocard_berndt_galway_chunk_1905
import Theorems.Thm_Brocard_berndt_galway_chunk_1906
import Theorems.Thm_Brocard_berndt_galway_chunk_1907
import Theorems.Thm_Brocard_berndt_galway_chunk_1908
import Theorems.Thm_Brocard_berndt_galway_chunk_1909
import Theorems.Thm_Brocard_berndt_galway_chunk_1910
import Theorems.Thm_Brocard_berndt_galway_chunk_1911
import Theorems.Thm_Brocard_berndt_galway_chunk_1912
import Theorems.Thm_Brocard_berndt_galway_chunk_1913
import Theorems.Thm_Brocard_berndt_galway_chunk_1914
import Theorems.Thm_Brocard_berndt_galway_chunk_1915
import Theorems.Thm_Brocard_berndt_galway_chunk_1916
import Theorems.Thm_Brocard_berndt_galway_chunk_1917
import Theorems.Thm_Brocard_berndt_galway_chunk_1918
import Theorems.Thm_Brocard_berndt_galway_chunk_1919
import Theorems.Thm_Brocard_berndt_galway_chunk_1920
import Theorems.Thm_Brocard_berndt_galway_chunk_1921
import Theorems.Thm_Brocard_berndt_galway_chunk_1922
import Theorems.Thm_Brocard_berndt_galway_chunk_1923
import Theorems.Thm_Brocard_berndt_galway_chunk_1924
import Theorems.Thm_Brocard_berndt_galway_chunk_1925
import Theorems.Thm_Brocard_berndt_galway_chunk_1926
import Theorems.Thm_Brocard_berndt_galway_chunk_1927
import Theorems.Thm_Brocard_berndt_galway_chunk_1928
import Theorems.Thm_Brocard_berndt_galway_chunk_1929
import Theorems.Thm_Brocard_berndt_galway_chunk_1930
import Theorems.Thm_Brocard_berndt_galway_chunk_1931
import Theorems.Thm_Brocard_berndt_galway_chunk_1932
import Theorems.Thm_Brocard_berndt_galway_chunk_1933
import Theorems.Thm_Brocard_berndt_galway_chunk_1934
import Theorems.Thm_Brocard_berndt_galway_chunk_1935
import Theorems.Thm_Brocard_berndt_galway_chunk_1936
import Theorems.Thm_Brocard_berndt_galway_chunk_1937
import Theorems.Thm_Brocard_berndt_galway_chunk_1938
import Theorems.Thm_Brocard_berndt_galway_chunk_1939
import Theorems.Thm_Brocard_berndt_galway_chunk_1940
import Theorems.Thm_Brocard_berndt_galway_chunk_1941
import Theorems.Thm_Brocard_berndt_galway_chunk_1942
import Theorems.Thm_Brocard_berndt_galway_chunk_1943
import Theorems.Thm_Brocard_berndt_galway_chunk_1944
import Theorems.Thm_Brocard_berndt_galway_chunk_1945
import Theorems.Thm_Brocard_berndt_galway_chunk_1946
import Theorems.Thm_Brocard_berndt_galway_chunk_1947
import Theorems.Thm_Brocard_berndt_galway_chunk_1948

theorem solution (n m : ℕ) (h1 : 342086330 ≤ n) (h2 : n < 350359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 346223021 with hs0 | hs0
  · -- n < 346223021
    rcases Nat.lt_or_ge n 344244604 with hs1 | hs1
    · -- n < 344244604
      rcases Nat.lt_or_ge n 343165467 with hs2 | hs2
      · -- n < 343165467
        rcases Nat.lt_or_ge n 342625899 with hs3 | hs3
        · -- n < 342625899
          rcases Nat.lt_or_ge n 342446043 with hs4 | hs4
          · -- n < 342446043
            rcases Nat.lt_or_ge n 342266187 with hs5 | hs5
            · -- n < 342266187
              exact Brocard.berndt_galway_chunk_1903 n m (by omega) (by omega) h
            · -- n >= 342266187
              exact Brocard.berndt_galway_chunk_1904 n m (by omega) (by omega) h
          · -- n >= 342446043
            exact Brocard.berndt_galway_chunk_1905 n m (by omega) (by omega) h
        · -- n >= 342625899
          rcases Nat.lt_or_ge n 342985611 with hs4 | hs4
          · -- n < 342985611
            rcases Nat.lt_or_ge n 342805755 with hs5 | hs5
            · -- n < 342805755
              exact Brocard.berndt_galway_chunk_1906 n m (by omega) (by omega) h
            · -- n >= 342805755
              exact Brocard.berndt_galway_chunk_1907 n m (by omega) (by omega) h
          · -- n >= 342985611
            exact Brocard.berndt_galway_chunk_1908 n m (by omega) (by omega) h
      · -- n >= 343165467
        rcases Nat.lt_or_ge n 343705035 with hs3 | hs3
        · -- n < 343705035
          rcases Nat.lt_or_ge n 343525179 with hs4 | hs4
          · -- n < 343525179
            rcases Nat.lt_or_ge n 343345323 with hs5 | hs5
            · -- n < 343345323
              exact Brocard.berndt_galway_chunk_1909 n m (by omega) (by omega) h
            · -- n >= 343345323
              exact Brocard.berndt_galway_chunk_1910 n m (by omega) (by omega) h
          · -- n >= 343525179
            exact Brocard.berndt_galway_chunk_1911 n m (by omega) (by omega) h
        · -- n >= 343705035
          rcases Nat.lt_or_ge n 344064748 with hs4 | hs4
          · -- n < 344064748
            rcases Nat.lt_or_ge n 343884892 with hs5 | hs5
            · -- n < 343884892
              exact Brocard.berndt_galway_chunk_1912 n m (by omega) (by omega) h
            · -- n >= 343884892
              exact Brocard.berndt_galway_chunk_1913 n m (by omega) (by omega) h
          · -- n >= 344064748
            exact Brocard.berndt_galway_chunk_1914 n m (by omega) (by omega) h
    · -- n >= 344244604
      rcases Nat.lt_or_ge n 345323741 with hs2 | hs2
      · -- n < 345323741
        rcases Nat.lt_or_ge n 344784172 with hs3 | hs3
        · -- n < 344784172
          rcases Nat.lt_or_ge n 344604316 with hs4 | hs4
          · -- n < 344604316
            rcases Nat.lt_or_ge n 344424460 with hs5 | hs5
            · -- n < 344424460
              exact Brocard.berndt_galway_chunk_1915 n m (by omega) (by omega) h
            · -- n >= 344424460
              exact Brocard.berndt_galway_chunk_1916 n m (by omega) (by omega) h
          · -- n >= 344604316
            exact Brocard.berndt_galway_chunk_1917 n m (by omega) (by omega) h
        · -- n >= 344784172
          rcases Nat.lt_or_ge n 345143884 with hs4 | hs4
          · -- n < 345143884
            rcases Nat.lt_or_ge n 344964028 with hs5 | hs5
            · -- n < 344964028
              exact Brocard.berndt_galway_chunk_1918 n m (by omega) (by omega) h
            · -- n >= 344964028
              exact Brocard.berndt_galway_chunk_1919 n m (by omega) (by omega) h
          · -- n >= 345143884
            exact Brocard.berndt_galway_chunk_1920 n m (by omega) (by omega) h
      · -- n >= 345323741
        rcases Nat.lt_or_ge n 345863309 with hs3 | hs3
        · -- n < 345863309
          rcases Nat.lt_or_ge n 345683453 with hs4 | hs4
          · -- n < 345683453
            rcases Nat.lt_or_ge n 345503597 with hs5 | hs5
            · -- n < 345503597
              exact Brocard.berndt_galway_chunk_1921 n m (by omega) (by omega) h
            · -- n >= 345503597
              exact Brocard.berndt_galway_chunk_1922 n m (by omega) (by omega) h
          · -- n >= 345683453
            exact Brocard.berndt_galway_chunk_1923 n m (by omega) (by omega) h
        · -- n >= 345863309
          rcases Nat.lt_or_ge n 346043165 with hs4 | hs4
          · -- n < 346043165
            exact Brocard.berndt_galway_chunk_1924 n m (by omega) (by omega) h
          · -- n >= 346043165
            exact Brocard.berndt_galway_chunk_1925 n m (by omega) (by omega) h
  · -- n >= 346223021
    rcases Nat.lt_or_ge n 348381294 with hs1 | hs1
    · -- n < 348381294
      rcases Nat.lt_or_ge n 347302158 with hs2 | hs2
      · -- n < 347302158
        rcases Nat.lt_or_ge n 346762589 with hs3 | hs3
        · -- n < 346762589
          rcases Nat.lt_or_ge n 346582733 with hs4 | hs4
          · -- n < 346582733
            rcases Nat.lt_or_ge n 346402877 with hs5 | hs5
            · -- n < 346402877
              exact Brocard.berndt_galway_chunk_1926 n m (by omega) (by omega) h
            · -- n >= 346402877
              exact Brocard.berndt_galway_chunk_1927 n m (by omega) (by omega) h
          · -- n >= 346582733
            exact Brocard.berndt_galway_chunk_1928 n m (by omega) (by omega) h
        · -- n >= 346762589
          rcases Nat.lt_or_ge n 347122302 with hs4 | hs4
          · -- n < 347122302
            rcases Nat.lt_or_ge n 346942446 with hs5 | hs5
            · -- n < 346942446
              exact Brocard.berndt_galway_chunk_1929 n m (by omega) (by omega) h
            · -- n >= 346942446
              exact Brocard.berndt_galway_chunk_1930 n m (by omega) (by omega) h
          · -- n >= 347122302
            exact Brocard.berndt_galway_chunk_1931 n m (by omega) (by omega) h
      · -- n >= 347302158
        rcases Nat.lt_or_ge n 347841726 with hs3 | hs3
        · -- n < 347841726
          rcases Nat.lt_or_ge n 347661870 with hs4 | hs4
          · -- n < 347661870
            rcases Nat.lt_or_ge n 347482014 with hs5 | hs5
            · -- n < 347482014
              exact Brocard.berndt_galway_chunk_1932 n m (by omega) (by omega) h
            · -- n >= 347482014
              exact Brocard.berndt_galway_chunk_1933 n m (by omega) (by omega) h
          · -- n >= 347661870
            exact Brocard.berndt_galway_chunk_1934 n m (by omega) (by omega) h
        · -- n >= 347841726
          rcases Nat.lt_or_ge n 348201438 with hs4 | hs4
          · -- n < 348201438
            rcases Nat.lt_or_ge n 348021582 with hs5 | hs5
            · -- n < 348021582
              exact Brocard.berndt_galway_chunk_1935 n m (by omega) (by omega) h
            · -- n >= 348021582
              exact Brocard.berndt_galway_chunk_1936 n m (by omega) (by omega) h
          · -- n >= 348201438
            exact Brocard.berndt_galway_chunk_1937 n m (by omega) (by omega) h
    · -- n >= 348381294
      rcases Nat.lt_or_ge n 349460431 with hs2 | hs2
      · -- n < 349460431
        rcases Nat.lt_or_ge n 348920863 with hs3 | hs3
        · -- n < 348920863
          rcases Nat.lt_or_ge n 348741007 with hs4 | hs4
          · -- n < 348741007
            rcases Nat.lt_or_ge n 348561151 with hs5 | hs5
            · -- n < 348561151
              exact Brocard.berndt_galway_chunk_1938 n m (by omega) (by omega) h
            · -- n >= 348561151
              exact Brocard.berndt_galway_chunk_1939 n m (by omega) (by omega) h
          · -- n >= 348741007
            exact Brocard.berndt_galway_chunk_1940 n m (by omega) (by omega) h
        · -- n >= 348920863
          rcases Nat.lt_or_ge n 349280575 with hs4 | hs4
          · -- n < 349280575
            rcases Nat.lt_or_ge n 349100719 with hs5 | hs5
            · -- n < 349100719
              exact Brocard.berndt_galway_chunk_1941 n m (by omega) (by omega) h
            · -- n >= 349100719
              exact Brocard.berndt_galway_chunk_1942 n m (by omega) (by omega) h
          · -- n >= 349280575
            exact Brocard.berndt_galway_chunk_1943 n m (by omega) (by omega) h
      · -- n >= 349460431
        rcases Nat.lt_or_ge n 350000000 with hs3 | hs3
        · -- n < 350000000
          rcases Nat.lt_or_ge n 349820143 with hs4 | hs4
          · -- n < 349820143
            rcases Nat.lt_or_ge n 349640287 with hs5 | hs5
            · -- n < 349640287
              exact Brocard.berndt_galway_chunk_1944 n m (by omega) (by omega) h
            · -- n >= 349640287
              exact Brocard.berndt_galway_chunk_1945 n m (by omega) (by omega) h
          · -- n >= 349820143
            exact Brocard.berndt_galway_chunk_1946 n m (by omega) (by omega) h
        · -- n >= 350000000
          rcases Nat.lt_or_ge n 350179856 with hs4 | hs4
          · -- n < 350179856
            exact Brocard.berndt_galway_chunk_1947 n m (by omega) (by omega) h
          · -- n >= 350179856
            exact Brocard.berndt_galway_chunk_1948 n m (by omega) (by omega) h

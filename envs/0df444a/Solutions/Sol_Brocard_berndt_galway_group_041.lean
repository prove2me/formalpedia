-- Prove2me | solution 1 for Brocard.berndt_galway_group_041
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:14:32.955577+00:00
-- url     : https://prove2.me/submissions/03d2de50-4829-4373-85b7-2facbf47435f

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1857
import Theorems.Thm_Brocard_berndt_galway_chunk_1858
import Theorems.Thm_Brocard_berndt_galway_chunk_1859
import Theorems.Thm_Brocard_berndt_galway_chunk_1860
import Theorems.Thm_Brocard_berndt_galway_chunk_1861
import Theorems.Thm_Brocard_berndt_galway_chunk_1862
import Theorems.Thm_Brocard_berndt_galway_chunk_1863
import Theorems.Thm_Brocard_berndt_galway_chunk_1864
import Theorems.Thm_Brocard_berndt_galway_chunk_1865
import Theorems.Thm_Brocard_berndt_galway_chunk_1866
import Theorems.Thm_Brocard_berndt_galway_chunk_1867
import Theorems.Thm_Brocard_berndt_galway_chunk_1868
import Theorems.Thm_Brocard_berndt_galway_chunk_1869
import Theorems.Thm_Brocard_berndt_galway_chunk_1870
import Theorems.Thm_Brocard_berndt_galway_chunk_1871
import Theorems.Thm_Brocard_berndt_galway_chunk_1872
import Theorems.Thm_Brocard_berndt_galway_chunk_1873
import Theorems.Thm_Brocard_berndt_galway_chunk_1874
import Theorems.Thm_Brocard_berndt_galway_chunk_1875
import Theorems.Thm_Brocard_berndt_galway_chunk_1876
import Theorems.Thm_Brocard_berndt_galway_chunk_1877
import Theorems.Thm_Brocard_berndt_galway_chunk_1878
import Theorems.Thm_Brocard_berndt_galway_chunk_1879
import Theorems.Thm_Brocard_berndt_galway_chunk_1880
import Theorems.Thm_Brocard_berndt_galway_chunk_1881
import Theorems.Thm_Brocard_berndt_galway_chunk_1882
import Theorems.Thm_Brocard_berndt_galway_chunk_1883
import Theorems.Thm_Brocard_berndt_galway_chunk_1884
import Theorems.Thm_Brocard_berndt_galway_chunk_1885
import Theorems.Thm_Brocard_berndt_galway_chunk_1886
import Theorems.Thm_Brocard_berndt_galway_chunk_1887
import Theorems.Thm_Brocard_berndt_galway_chunk_1888
import Theorems.Thm_Brocard_berndt_galway_chunk_1889
import Theorems.Thm_Brocard_berndt_galway_chunk_1890
import Theorems.Thm_Brocard_berndt_galway_chunk_1891
import Theorems.Thm_Brocard_berndt_galway_chunk_1892
import Theorems.Thm_Brocard_berndt_galway_chunk_1893
import Theorems.Thm_Brocard_berndt_galway_chunk_1894
import Theorems.Thm_Brocard_berndt_galway_chunk_1895
import Theorems.Thm_Brocard_berndt_galway_chunk_1896
import Theorems.Thm_Brocard_berndt_galway_chunk_1897
import Theorems.Thm_Brocard_berndt_galway_chunk_1898
import Theorems.Thm_Brocard_berndt_galway_chunk_1899
import Theorems.Thm_Brocard_berndt_galway_chunk_1900
import Theorems.Thm_Brocard_berndt_galway_chunk_1901
import Theorems.Thm_Brocard_berndt_galway_chunk_1902

theorem solution (n m : ℕ) (h1 : 333812949 ≤ n) (h2 : n < 342086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 337949640 with hs0 | hs0
  · -- n < 337949640
    rcases Nat.lt_or_ge n 335971223 with hs1 | hs1
    · -- n < 335971223
      rcases Nat.lt_or_ge n 334892086 with hs2 | hs2
      · -- n < 334892086
        rcases Nat.lt_or_ge n 334352517 with hs3 | hs3
        · -- n < 334352517
          rcases Nat.lt_or_ge n 334172661 with hs4 | hs4
          · -- n < 334172661
            rcases Nat.lt_or_ge n 333992805 with hs5 | hs5
            · -- n < 333992805
              exact Brocard.berndt_galway_chunk_1857 n m (by omega) (by omega) h
            · -- n >= 333992805
              exact Brocard.berndt_galway_chunk_1858 n m (by omega) (by omega) h
          · -- n >= 334172661
            exact Brocard.berndt_galway_chunk_1859 n m (by omega) (by omega) h
        · -- n >= 334352517
          rcases Nat.lt_or_ge n 334712230 with hs4 | hs4
          · -- n < 334712230
            rcases Nat.lt_or_ge n 334532374 with hs5 | hs5
            · -- n < 334532374
              exact Brocard.berndt_galway_chunk_1860 n m (by omega) (by omega) h
            · -- n >= 334532374
              exact Brocard.berndt_galway_chunk_1861 n m (by omega) (by omega) h
          · -- n >= 334712230
            exact Brocard.berndt_galway_chunk_1862 n m (by omega) (by omega) h
      · -- n >= 334892086
        rcases Nat.lt_or_ge n 335431654 with hs3 | hs3
        · -- n < 335431654
          rcases Nat.lt_or_ge n 335251798 with hs4 | hs4
          · -- n < 335251798
            rcases Nat.lt_or_ge n 335071942 with hs5 | hs5
            · -- n < 335071942
              exact Brocard.berndt_galway_chunk_1863 n m (by omega) (by omega) h
            · -- n >= 335071942
              exact Brocard.berndt_galway_chunk_1864 n m (by omega) (by omega) h
          · -- n >= 335251798
            exact Brocard.berndt_galway_chunk_1865 n m (by omega) (by omega) h
        · -- n >= 335431654
          rcases Nat.lt_or_ge n 335791366 with hs4 | hs4
          · -- n < 335791366
            rcases Nat.lt_or_ge n 335611510 with hs5 | hs5
            · -- n < 335611510
              exact Brocard.berndt_galway_chunk_1866 n m (by omega) (by omega) h
            · -- n >= 335611510
              exact Brocard.berndt_galway_chunk_1867 n m (by omega) (by omega) h
          · -- n >= 335791366
            exact Brocard.berndt_galway_chunk_1868 n m (by omega) (by omega) h
    · -- n >= 335971223
      rcases Nat.lt_or_ge n 337050359 with hs2 | hs2
      · -- n < 337050359
        rcases Nat.lt_or_ge n 336510791 with hs3 | hs3
        · -- n < 336510791
          rcases Nat.lt_or_ge n 336330935 with hs4 | hs4
          · -- n < 336330935
            rcases Nat.lt_or_ge n 336151079 with hs5 | hs5
            · -- n < 336151079
              exact Brocard.berndt_galway_chunk_1869 n m (by omega) (by omega) h
            · -- n >= 336151079
              exact Brocard.berndt_galway_chunk_1870 n m (by omega) (by omega) h
          · -- n >= 336330935
            exact Brocard.berndt_galway_chunk_1871 n m (by omega) (by omega) h
        · -- n >= 336510791
          rcases Nat.lt_or_ge n 336870503 with hs4 | hs4
          · -- n < 336870503
            rcases Nat.lt_or_ge n 336690647 with hs5 | hs5
            · -- n < 336690647
              exact Brocard.berndt_galway_chunk_1872 n m (by omega) (by omega) h
            · -- n >= 336690647
              exact Brocard.berndt_galway_chunk_1873 n m (by omega) (by omega) h
          · -- n >= 336870503
            exact Brocard.berndt_galway_chunk_1874 n m (by omega) (by omega) h
      · -- n >= 337050359
        rcases Nat.lt_or_ge n 337589928 with hs3 | hs3
        · -- n < 337589928
          rcases Nat.lt_or_ge n 337410071 with hs4 | hs4
          · -- n < 337410071
            rcases Nat.lt_or_ge n 337230215 with hs5 | hs5
            · -- n < 337230215
              exact Brocard.berndt_galway_chunk_1875 n m (by omega) (by omega) h
            · -- n >= 337230215
              exact Brocard.berndt_galway_chunk_1876 n m (by omega) (by omega) h
          · -- n >= 337410071
            exact Brocard.berndt_galway_chunk_1877 n m (by omega) (by omega) h
        · -- n >= 337589928
          rcases Nat.lt_or_ge n 337769784 with hs4 | hs4
          · -- n < 337769784
            exact Brocard.berndt_galway_chunk_1878 n m (by omega) (by omega) h
          · -- n >= 337769784
            exact Brocard.berndt_galway_chunk_1879 n m (by omega) (by omega) h
  · -- n >= 337949640
    rcases Nat.lt_or_ge n 340107913 with hs1 | hs1
    · -- n < 340107913
      rcases Nat.lt_or_ge n 339028776 with hs2 | hs2
      · -- n < 339028776
        rcases Nat.lt_or_ge n 338489208 with hs3 | hs3
        · -- n < 338489208
          rcases Nat.lt_or_ge n 338309352 with hs4 | hs4
          · -- n < 338309352
            rcases Nat.lt_or_ge n 338129496 with hs5 | hs5
            · -- n < 338129496
              exact Brocard.berndt_galway_chunk_1880 n m (by omega) (by omega) h
            · -- n >= 338129496
              exact Brocard.berndt_galway_chunk_1881 n m (by omega) (by omega) h
          · -- n >= 338309352
            exact Brocard.berndt_galway_chunk_1882 n m (by omega) (by omega) h
        · -- n >= 338489208
          rcases Nat.lt_or_ge n 338848920 with hs4 | hs4
          · -- n < 338848920
            rcases Nat.lt_or_ge n 338669064 with hs5 | hs5
            · -- n < 338669064
              exact Brocard.berndt_galway_chunk_1883 n m (by omega) (by omega) h
            · -- n >= 338669064
              exact Brocard.berndt_galway_chunk_1884 n m (by omega) (by omega) h
          · -- n >= 338848920
            exact Brocard.berndt_galway_chunk_1885 n m (by omega) (by omega) h
      · -- n >= 339028776
        rcases Nat.lt_or_ge n 339568345 with hs3 | hs3
        · -- n < 339568345
          rcases Nat.lt_or_ge n 339388489 with hs4 | hs4
          · -- n < 339388489
            rcases Nat.lt_or_ge n 339208633 with hs5 | hs5
            · -- n < 339208633
              exact Brocard.berndt_galway_chunk_1886 n m (by omega) (by omega) h
            · -- n >= 339208633
              exact Brocard.berndt_galway_chunk_1887 n m (by omega) (by omega) h
          · -- n >= 339388489
            exact Brocard.berndt_galway_chunk_1888 n m (by omega) (by omega) h
        · -- n >= 339568345
          rcases Nat.lt_or_ge n 339928057 with hs4 | hs4
          · -- n < 339928057
            rcases Nat.lt_or_ge n 339748201 with hs5 | hs5
            · -- n < 339748201
              exact Brocard.berndt_galway_chunk_1889 n m (by omega) (by omega) h
            · -- n >= 339748201
              exact Brocard.berndt_galway_chunk_1890 n m (by omega) (by omega) h
          · -- n >= 339928057
            exact Brocard.berndt_galway_chunk_1891 n m (by omega) (by omega) h
    · -- n >= 340107913
      rcases Nat.lt_or_ge n 341187050 with hs2 | hs2
      · -- n < 341187050
        rcases Nat.lt_or_ge n 340647482 with hs3 | hs3
        · -- n < 340647482
          rcases Nat.lt_or_ge n 340467625 with hs4 | hs4
          · -- n < 340467625
            rcases Nat.lt_or_ge n 340287769 with hs5 | hs5
            · -- n < 340287769
              exact Brocard.berndt_galway_chunk_1892 n m (by omega) (by omega) h
            · -- n >= 340287769
              exact Brocard.berndt_galway_chunk_1893 n m (by omega) (by omega) h
          · -- n >= 340467625
            exact Brocard.berndt_galway_chunk_1894 n m (by omega) (by omega) h
        · -- n >= 340647482
          rcases Nat.lt_or_ge n 341007194 with hs4 | hs4
          · -- n < 341007194
            rcases Nat.lt_or_ge n 340827338 with hs5 | hs5
            · -- n < 340827338
              exact Brocard.berndt_galway_chunk_1895 n m (by omega) (by omega) h
            · -- n >= 340827338
              exact Brocard.berndt_galway_chunk_1896 n m (by omega) (by omega) h
          · -- n >= 341007194
            exact Brocard.berndt_galway_chunk_1897 n m (by omega) (by omega) h
      · -- n >= 341187050
        rcases Nat.lt_or_ge n 341726618 with hs3 | hs3
        · -- n < 341726618
          rcases Nat.lt_or_ge n 341546762 with hs4 | hs4
          · -- n < 341546762
            rcases Nat.lt_or_ge n 341366906 with hs5 | hs5
            · -- n < 341366906
              exact Brocard.berndt_galway_chunk_1898 n m (by omega) (by omega) h
            · -- n >= 341366906
              exact Brocard.berndt_galway_chunk_1899 n m (by omega) (by omega) h
          · -- n >= 341546762
            exact Brocard.berndt_galway_chunk_1900 n m (by omega) (by omega) h
        · -- n >= 341726618
          rcases Nat.lt_or_ge n 341906474 with hs4 | hs4
          · -- n < 341906474
            exact Brocard.berndt_galway_chunk_1901 n m (by omega) (by omega) h
          · -- n >= 341906474
            exact Brocard.berndt_galway_chunk_1902 n m (by omega) (by omega) h

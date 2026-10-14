-- Prove2me | solution 1 for Brocard.berndt_galway_group_040
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:00:40.393973+00:00
-- url     : https://prove2.me/submissions/5a4ba6a9-c620-4711-bfd6-70bd5a847ef0

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1810
import Theorems.Thm_Brocard_berndt_galway_chunk_1811
import Theorems.Thm_Brocard_berndt_galway_chunk_1812
import Theorems.Thm_Brocard_berndt_galway_chunk_1813
import Theorems.Thm_Brocard_berndt_galway_chunk_1814
import Theorems.Thm_Brocard_berndt_galway_chunk_1815
import Theorems.Thm_Brocard_berndt_galway_chunk_1816
import Theorems.Thm_Brocard_berndt_galway_chunk_1817
import Theorems.Thm_Brocard_berndt_galway_chunk_1818
import Theorems.Thm_Brocard_berndt_galway_chunk_1819
import Theorems.Thm_Brocard_berndt_galway_chunk_1820
import Theorems.Thm_Brocard_berndt_galway_chunk_1821
import Theorems.Thm_Brocard_berndt_galway_chunk_1822
import Theorems.Thm_Brocard_berndt_galway_chunk_1823
import Theorems.Thm_Brocard_berndt_galway_chunk_1824
import Theorems.Thm_Brocard_berndt_galway_chunk_1825
import Theorems.Thm_Brocard_berndt_galway_chunk_1826
import Theorems.Thm_Brocard_berndt_galway_chunk_1827
import Theorems.Thm_Brocard_berndt_galway_chunk_1828
import Theorems.Thm_Brocard_berndt_galway_chunk_1829
import Theorems.Thm_Brocard_berndt_galway_chunk_1830
import Theorems.Thm_Brocard_berndt_galway_chunk_1831
import Theorems.Thm_Brocard_berndt_galway_chunk_1832
import Theorems.Thm_Brocard_berndt_galway_chunk_1833
import Theorems.Thm_Brocard_berndt_galway_chunk_1834
import Theorems.Thm_Brocard_berndt_galway_chunk_1835
import Theorems.Thm_Brocard_berndt_galway_chunk_1836
import Theorems.Thm_Brocard_berndt_galway_chunk_1837
import Theorems.Thm_Brocard_berndt_galway_chunk_1838
import Theorems.Thm_Brocard_berndt_galway_chunk_1839
import Theorems.Thm_Brocard_berndt_galway_chunk_1840
import Theorems.Thm_Brocard_berndt_galway_chunk_1841
import Theorems.Thm_Brocard_berndt_galway_chunk_1842
import Theorems.Thm_Brocard_berndt_galway_chunk_1843
import Theorems.Thm_Brocard_berndt_galway_chunk_1844
import Theorems.Thm_Brocard_berndt_galway_chunk_1845
import Theorems.Thm_Brocard_berndt_galway_chunk_1846
import Theorems.Thm_Brocard_berndt_galway_chunk_1847
import Theorems.Thm_Brocard_berndt_galway_chunk_1848
import Theorems.Thm_Brocard_berndt_galway_chunk_1849
import Theorems.Thm_Brocard_berndt_galway_chunk_1850
import Theorems.Thm_Brocard_berndt_galway_chunk_1851
import Theorems.Thm_Brocard_berndt_galway_chunk_1852
import Theorems.Thm_Brocard_berndt_galway_chunk_1853
import Theorems.Thm_Brocard_berndt_galway_chunk_1854
import Theorems.Thm_Brocard_berndt_galway_chunk_1855
import Theorems.Thm_Brocard_berndt_galway_chunk_1856

theorem solution (n m : ℕ) (h1 : 325359712 ≤ n) (h2 : n < 333812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 329676258 with hs0 | hs0
  · -- n < 329676258
    rcases Nat.lt_or_ge n 327517985 with hs1 | hs1
    · -- n < 327517985
      rcases Nat.lt_or_ge n 326438848 with hs2 | hs2
      · -- n < 326438848
        rcases Nat.lt_or_ge n 325899280 with hs3 | hs3
        · -- n < 325899280
          rcases Nat.lt_or_ge n 325719424 with hs4 | hs4
          · -- n < 325719424
            rcases Nat.lt_or_ge n 325539568 with hs5 | hs5
            · -- n < 325539568
              exact Brocard.berndt_galway_chunk_1810 n m (by omega) (by omega) h
            · -- n >= 325539568
              exact Brocard.berndt_galway_chunk_1811 n m (by omega) (by omega) h
          · -- n >= 325719424
            exact Brocard.berndt_galway_chunk_1812 n m (by omega) (by omega) h
        · -- n >= 325899280
          rcases Nat.lt_or_ge n 326258992 with hs4 | hs4
          · -- n < 326258992
            rcases Nat.lt_or_ge n 326079136 with hs5 | hs5
            · -- n < 326079136
              exact Brocard.berndt_galway_chunk_1813 n m (by omega) (by omega) h
            · -- n >= 326079136
              exact Brocard.berndt_galway_chunk_1814 n m (by omega) (by omega) h
          · -- n >= 326258992
            exact Brocard.berndt_galway_chunk_1815 n m (by omega) (by omega) h
      · -- n >= 326438848
        rcases Nat.lt_or_ge n 326978417 with hs3 | hs3
        · -- n < 326978417
          rcases Nat.lt_or_ge n 326798561 with hs4 | hs4
          · -- n < 326798561
            rcases Nat.lt_or_ge n 326618705 with hs5 | hs5
            · -- n < 326618705
              exact Brocard.berndt_galway_chunk_1816 n m (by omega) (by omega) h
            · -- n >= 326618705
              exact Brocard.berndt_galway_chunk_1817 n m (by omega) (by omega) h
          · -- n >= 326798561
            exact Brocard.berndt_galway_chunk_1818 n m (by omega) (by omega) h
        · -- n >= 326978417
          rcases Nat.lt_or_ge n 327338129 with hs4 | hs4
          · -- n < 327338129
            rcases Nat.lt_or_ge n 327158273 with hs5 | hs5
            · -- n < 327158273
              exact Brocard.berndt_galway_chunk_1819 n m (by omega) (by omega) h
            · -- n >= 327158273
              exact Brocard.berndt_galway_chunk_1820 n m (by omega) (by omega) h
          · -- n >= 327338129
            exact Brocard.berndt_galway_chunk_1821 n m (by omega) (by omega) h
    · -- n >= 327517985
      rcases Nat.lt_or_ge n 328597122 with hs2 | hs2
      · -- n < 328597122
        rcases Nat.lt_or_ge n 328057553 with hs3 | hs3
        · -- n < 328057553
          rcases Nat.lt_or_ge n 327877697 with hs4 | hs4
          · -- n < 327877697
            rcases Nat.lt_or_ge n 327697841 with hs5 | hs5
            · -- n < 327697841
              exact Brocard.berndt_galway_chunk_1822 n m (by omega) (by omega) h
            · -- n >= 327697841
              exact Brocard.berndt_galway_chunk_1823 n m (by omega) (by omega) h
          · -- n >= 327877697
            exact Brocard.berndt_galway_chunk_1824 n m (by omega) (by omega) h
        · -- n >= 328057553
          rcases Nat.lt_or_ge n 328417266 with hs4 | hs4
          · -- n < 328417266
            rcases Nat.lt_or_ge n 328237410 with hs5 | hs5
            · -- n < 328237410
              exact Brocard.berndt_galway_chunk_1825 n m (by omega) (by omega) h
            · -- n >= 328237410
              exact Brocard.berndt_galway_chunk_1826 n m (by omega) (by omega) h
          · -- n >= 328417266
            exact Brocard.berndt_galway_chunk_1827 n m (by omega) (by omega) h
      · -- n >= 328597122
        rcases Nat.lt_or_ge n 329136690 with hs3 | hs3
        · -- n < 329136690
          rcases Nat.lt_or_ge n 328956834 with hs4 | hs4
          · -- n < 328956834
            rcases Nat.lt_or_ge n 328776978 with hs5 | hs5
            · -- n < 328776978
              exact Brocard.berndt_galway_chunk_1828 n m (by omega) (by omega) h
            · -- n >= 328776978
              exact Brocard.berndt_galway_chunk_1829 n m (by omega) (by omega) h
          · -- n >= 328956834
            exact Brocard.berndt_galway_chunk_1830 n m (by omega) (by omega) h
        · -- n >= 329136690
          rcases Nat.lt_or_ge n 329496402 with hs4 | hs4
          · -- n < 329496402
            rcases Nat.lt_or_ge n 329316546 with hs5 | hs5
            · -- n < 329316546
              exact Brocard.berndt_galway_chunk_1831 n m (by omega) (by omega) h
            · -- n >= 329316546
              exact Brocard.berndt_galway_chunk_1832 n m (by omega) (by omega) h
          · -- n >= 329496402
            exact Brocard.berndt_galway_chunk_1833 n m (by omega) (by omega) h
  · -- n >= 329676258
    rcases Nat.lt_or_ge n 331834532 with hs1 | hs1
    · -- n < 331834532
      rcases Nat.lt_or_ge n 330755395 with hs2 | hs2
      · -- n < 330755395
        rcases Nat.lt_or_ge n 330215827 with hs3 | hs3
        · -- n < 330215827
          rcases Nat.lt_or_ge n 330035971 with hs4 | hs4
          · -- n < 330035971
            rcases Nat.lt_or_ge n 329856115 with hs5 | hs5
            · -- n < 329856115
              exact Brocard.berndt_galway_chunk_1834 n m (by omega) (by omega) h
            · -- n >= 329856115
              exact Brocard.berndt_galway_chunk_1835 n m (by omega) (by omega) h
          · -- n >= 330035971
            exact Brocard.berndt_galway_chunk_1836 n m (by omega) (by omega) h
        · -- n >= 330215827
          rcases Nat.lt_or_ge n 330575539 with hs4 | hs4
          · -- n < 330575539
            rcases Nat.lt_or_ge n 330395683 with hs5 | hs5
            · -- n < 330395683
              exact Brocard.berndt_galway_chunk_1837 n m (by omega) (by omega) h
            · -- n >= 330395683
              exact Brocard.berndt_galway_chunk_1838 n m (by omega) (by omega) h
          · -- n >= 330575539
            exact Brocard.berndt_galway_chunk_1839 n m (by omega) (by omega) h
      · -- n >= 330755395
        rcases Nat.lt_or_ge n 331294964 with hs3 | hs3
        · -- n < 331294964
          rcases Nat.lt_or_ge n 331115107 with hs4 | hs4
          · -- n < 331115107
            rcases Nat.lt_or_ge n 330935251 with hs5 | hs5
            · -- n < 330935251
              exact Brocard.berndt_galway_chunk_1840 n m (by omega) (by omega) h
            · -- n >= 330935251
              exact Brocard.berndt_galway_chunk_1841 n m (by omega) (by omega) h
          · -- n >= 331115107
            exact Brocard.berndt_galway_chunk_1842 n m (by omega) (by omega) h
        · -- n >= 331294964
          rcases Nat.lt_or_ge n 331654676 with hs4 | hs4
          · -- n < 331654676
            rcases Nat.lt_or_ge n 331474820 with hs5 | hs5
            · -- n < 331474820
              exact Brocard.berndt_galway_chunk_1843 n m (by omega) (by omega) h
            · -- n >= 331474820
              exact Brocard.berndt_galway_chunk_1844 n m (by omega) (by omega) h
          · -- n >= 331654676
            exact Brocard.berndt_galway_chunk_1845 n m (by omega) (by omega) h
    · -- n >= 331834532
      rcases Nat.lt_or_ge n 332913669 with hs2 | hs2
      · -- n < 332913669
        rcases Nat.lt_or_ge n 332374100 with hs3 | hs3
        · -- n < 332374100
          rcases Nat.lt_or_ge n 332194244 with hs4 | hs4
          · -- n < 332194244
            rcases Nat.lt_or_ge n 332014388 with hs5 | hs5
            · -- n < 332014388
              exact Brocard.berndt_galway_chunk_1846 n m (by omega) (by omega) h
            · -- n >= 332014388
              exact Brocard.berndt_galway_chunk_1847 n m (by omega) (by omega) h
          · -- n >= 332194244
            exact Brocard.berndt_galway_chunk_1848 n m (by omega) (by omega) h
        · -- n >= 332374100
          rcases Nat.lt_or_ge n 332733812 with hs4 | hs4
          · -- n < 332733812
            rcases Nat.lt_or_ge n 332553956 with hs5 | hs5
            · -- n < 332553956
              exact Brocard.berndt_galway_chunk_1849 n m (by omega) (by omega) h
            · -- n >= 332553956
              exact Brocard.berndt_galway_chunk_1850 n m (by omega) (by omega) h
          · -- n >= 332733812
            exact Brocard.berndt_galway_chunk_1851 n m (by omega) (by omega) h
      · -- n >= 332913669
        rcases Nat.lt_or_ge n 333453237 with hs3 | hs3
        · -- n < 333453237
          rcases Nat.lt_or_ge n 333273381 with hs4 | hs4
          · -- n < 333273381
            rcases Nat.lt_or_ge n 333093525 with hs5 | hs5
            · -- n < 333093525
              exact Brocard.berndt_galway_chunk_1852 n m (by omega) (by omega) h
            · -- n >= 333093525
              exact Brocard.berndt_galway_chunk_1853 n m (by omega) (by omega) h
          · -- n >= 333273381
            exact Brocard.berndt_galway_chunk_1854 n m (by omega) (by omega) h
        · -- n >= 333453237
          rcases Nat.lt_or_ge n 333633093 with hs4 | hs4
          · -- n < 333633093
            exact Brocard.berndt_galway_chunk_1855 n m (by omega) (by omega) h
          · -- n >= 333633093
            exact Brocard.berndt_galway_chunk_1856 n m (by omega) (by omega) h

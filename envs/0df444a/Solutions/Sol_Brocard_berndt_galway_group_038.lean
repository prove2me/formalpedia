-- Prove2me | solution 1 for Brocard.berndt_galway_group_038
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:43:18.973652+00:00
-- url     : https://prove2.me/submissions/c4c4c519-46f1-4510-bc39-27fe2dd3865a

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1716
import Theorems.Thm_Brocard_berndt_galway_chunk_1717
import Theorems.Thm_Brocard_berndt_galway_chunk_1718
import Theorems.Thm_Brocard_berndt_galway_chunk_1719
import Theorems.Thm_Brocard_berndt_galway_chunk_1720
import Theorems.Thm_Brocard_berndt_galway_chunk_1721
import Theorems.Thm_Brocard_berndt_galway_chunk_1722
import Theorems.Thm_Brocard_berndt_galway_chunk_1723
import Theorems.Thm_Brocard_berndt_galway_chunk_1724
import Theorems.Thm_Brocard_berndt_galway_chunk_1725
import Theorems.Thm_Brocard_berndt_galway_chunk_1726
import Theorems.Thm_Brocard_berndt_galway_chunk_1727
import Theorems.Thm_Brocard_berndt_galway_chunk_1728
import Theorems.Thm_Brocard_berndt_galway_chunk_1729
import Theorems.Thm_Brocard_berndt_galway_chunk_1730
import Theorems.Thm_Brocard_berndt_galway_chunk_1731
import Theorems.Thm_Brocard_berndt_galway_chunk_1732
import Theorems.Thm_Brocard_berndt_galway_chunk_1733
import Theorems.Thm_Brocard_berndt_galway_chunk_1734
import Theorems.Thm_Brocard_berndt_galway_chunk_1735
import Theorems.Thm_Brocard_berndt_galway_chunk_1736
import Theorems.Thm_Brocard_berndt_galway_chunk_1737
import Theorems.Thm_Brocard_berndt_galway_chunk_1738
import Theorems.Thm_Brocard_berndt_galway_chunk_1739
import Theorems.Thm_Brocard_berndt_galway_chunk_1740
import Theorems.Thm_Brocard_berndt_galway_chunk_1741
import Theorems.Thm_Brocard_berndt_galway_chunk_1742
import Theorems.Thm_Brocard_berndt_galway_chunk_1743
import Theorems.Thm_Brocard_berndt_galway_chunk_1744
import Theorems.Thm_Brocard_berndt_galway_chunk_1745
import Theorems.Thm_Brocard_berndt_galway_chunk_1746
import Theorems.Thm_Brocard_berndt_galway_chunk_1747
import Theorems.Thm_Brocard_berndt_galway_chunk_1748
import Theorems.Thm_Brocard_berndt_galway_chunk_1749
import Theorems.Thm_Brocard_berndt_galway_chunk_1750
import Theorems.Thm_Brocard_berndt_galway_chunk_1751
import Theorems.Thm_Brocard_berndt_galway_chunk_1752
import Theorems.Thm_Brocard_berndt_galway_chunk_1753
import Theorems.Thm_Brocard_berndt_galway_chunk_1754
import Theorems.Thm_Brocard_berndt_galway_chunk_1755
import Theorems.Thm_Brocard_berndt_galway_chunk_1756
import Theorems.Thm_Brocard_berndt_galway_chunk_1757
import Theorems.Thm_Brocard_berndt_galway_chunk_1758
import Theorems.Thm_Brocard_berndt_galway_chunk_1759
import Theorems.Thm_Brocard_berndt_galway_chunk_1760
import Theorems.Thm_Brocard_berndt_galway_chunk_1761
import Theorems.Thm_Brocard_berndt_galway_chunk_1762

theorem solution (n m : ℕ) (h1 : 308453237 ≤ n) (h2 : n < 316906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 312769784 with hs0 | hs0
  · -- n < 312769784
    rcases Nat.lt_or_ge n 310611510 with hs1 | hs1
    · -- n < 310611510
      rcases Nat.lt_or_ge n 309532374 with hs2 | hs2
      · -- n < 309532374
        rcases Nat.lt_or_ge n 308992805 with hs3 | hs3
        · -- n < 308992805
          rcases Nat.lt_or_ge n 308812949 with hs4 | hs4
          · -- n < 308812949
            rcases Nat.lt_or_ge n 308633093 with hs5 | hs5
            · -- n < 308633093
              exact Brocard.berndt_galway_chunk_1716 n m (by omega) (by omega) h
            · -- n >= 308633093
              exact Brocard.berndt_galway_chunk_1717 n m (by omega) (by omega) h
          · -- n >= 308812949
            exact Brocard.berndt_galway_chunk_1718 n m (by omega) (by omega) h
        · -- n >= 308992805
          rcases Nat.lt_or_ge n 309352517 with hs4 | hs4
          · -- n < 309352517
            rcases Nat.lt_or_ge n 309172661 with hs5 | hs5
            · -- n < 309172661
              exact Brocard.berndt_galway_chunk_1719 n m (by omega) (by omega) h
            · -- n >= 309172661
              exact Brocard.berndt_galway_chunk_1720 n m (by omega) (by omega) h
          · -- n >= 309352517
            exact Brocard.berndt_galway_chunk_1721 n m (by omega) (by omega) h
      · -- n >= 309532374
        rcases Nat.lt_or_ge n 310071942 with hs3 | hs3
        · -- n < 310071942
          rcases Nat.lt_or_ge n 309892086 with hs4 | hs4
          · -- n < 309892086
            rcases Nat.lt_or_ge n 309712230 with hs5 | hs5
            · -- n < 309712230
              exact Brocard.berndt_galway_chunk_1722 n m (by omega) (by omega) h
            · -- n >= 309712230
              exact Brocard.berndt_galway_chunk_1723 n m (by omega) (by omega) h
          · -- n >= 309892086
            exact Brocard.berndt_galway_chunk_1724 n m (by omega) (by omega) h
        · -- n >= 310071942
          rcases Nat.lt_or_ge n 310431654 with hs4 | hs4
          · -- n < 310431654
            rcases Nat.lt_or_ge n 310251798 with hs5 | hs5
            · -- n < 310251798
              exact Brocard.berndt_galway_chunk_1725 n m (by omega) (by omega) h
            · -- n >= 310251798
              exact Brocard.berndt_galway_chunk_1726 n m (by omega) (by omega) h
          · -- n >= 310431654
            exact Brocard.berndt_galway_chunk_1727 n m (by omega) (by omega) h
    · -- n >= 310611510
      rcases Nat.lt_or_ge n 311690647 with hs2 | hs2
      · -- n < 311690647
        rcases Nat.lt_or_ge n 311151079 with hs3 | hs3
        · -- n < 311151079
          rcases Nat.lt_or_ge n 310971223 with hs4 | hs4
          · -- n < 310971223
            rcases Nat.lt_or_ge n 310791366 with hs5 | hs5
            · -- n < 310791366
              exact Brocard.berndt_galway_chunk_1728 n m (by omega) (by omega) h
            · -- n >= 310791366
              exact Brocard.berndt_galway_chunk_1729 n m (by omega) (by omega) h
          · -- n >= 310971223
            exact Brocard.berndt_galway_chunk_1730 n m (by omega) (by omega) h
        · -- n >= 311151079
          rcases Nat.lt_or_ge n 311510791 with hs4 | hs4
          · -- n < 311510791
            rcases Nat.lt_or_ge n 311330935 with hs5 | hs5
            · -- n < 311330935
              exact Brocard.berndt_galway_chunk_1731 n m (by omega) (by omega) h
            · -- n >= 311330935
              exact Brocard.berndt_galway_chunk_1732 n m (by omega) (by omega) h
          · -- n >= 311510791
            exact Brocard.berndt_galway_chunk_1733 n m (by omega) (by omega) h
      · -- n >= 311690647
        rcases Nat.lt_or_ge n 312230215 with hs3 | hs3
        · -- n < 312230215
          rcases Nat.lt_or_ge n 312050359 with hs4 | hs4
          · -- n < 312050359
            rcases Nat.lt_or_ge n 311870503 with hs5 | hs5
            · -- n < 311870503
              exact Brocard.berndt_galway_chunk_1734 n m (by omega) (by omega) h
            · -- n >= 311870503
              exact Brocard.berndt_galway_chunk_1735 n m (by omega) (by omega) h
          · -- n >= 312050359
            exact Brocard.berndt_galway_chunk_1736 n m (by omega) (by omega) h
        · -- n >= 312230215
          rcases Nat.lt_or_ge n 312589928 with hs4 | hs4
          · -- n < 312589928
            rcases Nat.lt_or_ge n 312410071 with hs5 | hs5
            · -- n < 312410071
              exact Brocard.berndt_galway_chunk_1737 n m (by omega) (by omega) h
            · -- n >= 312410071
              exact Brocard.berndt_galway_chunk_1738 n m (by omega) (by omega) h
          · -- n >= 312589928
            exact Brocard.berndt_galway_chunk_1739 n m (by omega) (by omega) h
  · -- n >= 312769784
    rcases Nat.lt_or_ge n 314928057 with hs1 | hs1
    · -- n < 314928057
      rcases Nat.lt_or_ge n 313848920 with hs2 | hs2
      · -- n < 313848920
        rcases Nat.lt_or_ge n 313309352 with hs3 | hs3
        · -- n < 313309352
          rcases Nat.lt_or_ge n 313129496 with hs4 | hs4
          · -- n < 313129496
            rcases Nat.lt_or_ge n 312949640 with hs5 | hs5
            · -- n < 312949640
              exact Brocard.berndt_galway_chunk_1740 n m (by omega) (by omega) h
            · -- n >= 312949640
              exact Brocard.berndt_galway_chunk_1741 n m (by omega) (by omega) h
          · -- n >= 313129496
            exact Brocard.berndt_galway_chunk_1742 n m (by omega) (by omega) h
        · -- n >= 313309352
          rcases Nat.lt_or_ge n 313669064 with hs4 | hs4
          · -- n < 313669064
            rcases Nat.lt_or_ge n 313489208 with hs5 | hs5
            · -- n < 313489208
              exact Brocard.berndt_galway_chunk_1743 n m (by omega) (by omega) h
            · -- n >= 313489208
              exact Brocard.berndt_galway_chunk_1744 n m (by omega) (by omega) h
          · -- n >= 313669064
            exact Brocard.berndt_galway_chunk_1745 n m (by omega) (by omega) h
      · -- n >= 313848920
        rcases Nat.lt_or_ge n 314388489 with hs3 | hs3
        · -- n < 314388489
          rcases Nat.lt_or_ge n 314208633 with hs4 | hs4
          · -- n < 314208633
            rcases Nat.lt_or_ge n 314028776 with hs5 | hs5
            · -- n < 314028776
              exact Brocard.berndt_galway_chunk_1746 n m (by omega) (by omega) h
            · -- n >= 314028776
              exact Brocard.berndt_galway_chunk_1747 n m (by omega) (by omega) h
          · -- n >= 314208633
            exact Brocard.berndt_galway_chunk_1748 n m (by omega) (by omega) h
        · -- n >= 314388489
          rcases Nat.lt_or_ge n 314748201 with hs4 | hs4
          · -- n < 314748201
            rcases Nat.lt_or_ge n 314568345 with hs5 | hs5
            · -- n < 314568345
              exact Brocard.berndt_galway_chunk_1749 n m (by omega) (by omega) h
            · -- n >= 314568345
              exact Brocard.berndt_galway_chunk_1750 n m (by omega) (by omega) h
          · -- n >= 314748201
            exact Brocard.berndt_galway_chunk_1751 n m (by omega) (by omega) h
    · -- n >= 314928057
      rcases Nat.lt_or_ge n 316007194 with hs2 | hs2
      · -- n < 316007194
        rcases Nat.lt_or_ge n 315467625 with hs3 | hs3
        · -- n < 315467625
          rcases Nat.lt_or_ge n 315287769 with hs4 | hs4
          · -- n < 315287769
            rcases Nat.lt_or_ge n 315107913 with hs5 | hs5
            · -- n < 315107913
              exact Brocard.berndt_galway_chunk_1752 n m (by omega) (by omega) h
            · -- n >= 315107913
              exact Brocard.berndt_galway_chunk_1753 n m (by omega) (by omega) h
          · -- n >= 315287769
            exact Brocard.berndt_galway_chunk_1754 n m (by omega) (by omega) h
        · -- n >= 315467625
          rcases Nat.lt_or_ge n 315827338 with hs4 | hs4
          · -- n < 315827338
            rcases Nat.lt_or_ge n 315647482 with hs5 | hs5
            · -- n < 315647482
              exact Brocard.berndt_galway_chunk_1755 n m (by omega) (by omega) h
            · -- n >= 315647482
              exact Brocard.berndt_galway_chunk_1756 n m (by omega) (by omega) h
          · -- n >= 315827338
            exact Brocard.berndt_galway_chunk_1757 n m (by omega) (by omega) h
      · -- n >= 316007194
        rcases Nat.lt_or_ge n 316546762 with hs3 | hs3
        · -- n < 316546762
          rcases Nat.lt_or_ge n 316366906 with hs4 | hs4
          · -- n < 316366906
            rcases Nat.lt_or_ge n 316187050 with hs5 | hs5
            · -- n < 316187050
              exact Brocard.berndt_galway_chunk_1758 n m (by omega) (by omega) h
            · -- n >= 316187050
              exact Brocard.berndt_galway_chunk_1759 n m (by omega) (by omega) h
          · -- n >= 316366906
            exact Brocard.berndt_galway_chunk_1760 n m (by omega) (by omega) h
        · -- n >= 316546762
          rcases Nat.lt_or_ge n 316726618 with hs4 | hs4
          · -- n < 316726618
            exact Brocard.berndt_galway_chunk_1761 n m (by omega) (by omega) h
          · -- n >= 316726618
            exact Brocard.berndt_galway_chunk_1762 n m (by omega) (by omega) h

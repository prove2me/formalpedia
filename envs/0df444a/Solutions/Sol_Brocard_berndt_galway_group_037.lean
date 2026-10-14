-- Prove2me | solution 1 for Brocard.berndt_galway_group_037
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:29:42.758977+00:00
-- url     : https://prove2.me/submissions/ad482e94-77bb-4f34-81f0-2014e05b9373

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1669
import Theorems.Thm_Brocard_berndt_galway_chunk_1670
import Theorems.Thm_Brocard_berndt_galway_chunk_1671
import Theorems.Thm_Brocard_berndt_galway_chunk_1672
import Theorems.Thm_Brocard_berndt_galway_chunk_1673
import Theorems.Thm_Brocard_berndt_galway_chunk_1674
import Theorems.Thm_Brocard_berndt_galway_chunk_1675
import Theorems.Thm_Brocard_berndt_galway_chunk_1676
import Theorems.Thm_Brocard_berndt_galway_chunk_1677
import Theorems.Thm_Brocard_berndt_galway_chunk_1678
import Theorems.Thm_Brocard_berndt_galway_chunk_1679
import Theorems.Thm_Brocard_berndt_galway_chunk_1680
import Theorems.Thm_Brocard_berndt_galway_chunk_1681
import Theorems.Thm_Brocard_berndt_galway_chunk_1682
import Theorems.Thm_Brocard_berndt_galway_chunk_1683
import Theorems.Thm_Brocard_berndt_galway_chunk_1684
import Theorems.Thm_Brocard_berndt_galway_chunk_1685
import Theorems.Thm_Brocard_berndt_galway_chunk_1686
import Theorems.Thm_Brocard_berndt_galway_chunk_1687
import Theorems.Thm_Brocard_berndt_galway_chunk_1688
import Theorems.Thm_Brocard_berndt_galway_chunk_1689
import Theorems.Thm_Brocard_berndt_galway_chunk_1690
import Theorems.Thm_Brocard_berndt_galway_chunk_1691
import Theorems.Thm_Brocard_berndt_galway_chunk_1692
import Theorems.Thm_Brocard_berndt_galway_chunk_1693
import Theorems.Thm_Brocard_berndt_galway_chunk_1694
import Theorems.Thm_Brocard_berndt_galway_chunk_1695
import Theorems.Thm_Brocard_berndt_galway_chunk_1696
import Theorems.Thm_Brocard_berndt_galway_chunk_1697
import Theorems.Thm_Brocard_berndt_galway_chunk_1698
import Theorems.Thm_Brocard_berndt_galway_chunk_1699
import Theorems.Thm_Brocard_berndt_galway_chunk_1700
import Theorems.Thm_Brocard_berndt_galway_chunk_1701
import Theorems.Thm_Brocard_berndt_galway_chunk_1702
import Theorems.Thm_Brocard_berndt_galway_chunk_1703
import Theorems.Thm_Brocard_berndt_galway_chunk_1704
import Theorems.Thm_Brocard_berndt_galway_chunk_1705
import Theorems.Thm_Brocard_berndt_galway_chunk_1706
import Theorems.Thm_Brocard_berndt_galway_chunk_1707
import Theorems.Thm_Brocard_berndt_galway_chunk_1708
import Theorems.Thm_Brocard_berndt_galway_chunk_1709
import Theorems.Thm_Brocard_berndt_galway_chunk_1710
import Theorems.Thm_Brocard_berndt_galway_chunk_1711
import Theorems.Thm_Brocard_berndt_galway_chunk_1712
import Theorems.Thm_Brocard_berndt_galway_chunk_1713
import Theorems.Thm_Brocard_berndt_galway_chunk_1714
import Theorems.Thm_Brocard_berndt_galway_chunk_1715

theorem solution (n m : ℕ) (h1 : 300000000 ≤ n) (h2 : n < 308453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 304316546 with hs0 | hs0
  · -- n < 304316546
    rcases Nat.lt_or_ge n 302158273 with hs1 | hs1
    · -- n < 302158273
      rcases Nat.lt_or_ge n 301079136 with hs2 | hs2
      · -- n < 301079136
        rcases Nat.lt_or_ge n 300539568 with hs3 | hs3
        · -- n < 300539568
          rcases Nat.lt_or_ge n 300359712 with hs4 | hs4
          · -- n < 300359712
            rcases Nat.lt_or_ge n 300179856 with hs5 | hs5
            · -- n < 300179856
              exact Brocard.berndt_galway_chunk_1669 n m (by omega) (by omega) h
            · -- n >= 300179856
              exact Brocard.berndt_galway_chunk_1670 n m (by omega) (by omega) h
          · -- n >= 300359712
            exact Brocard.berndt_galway_chunk_1671 n m (by omega) (by omega) h
        · -- n >= 300539568
          rcases Nat.lt_or_ge n 300899280 with hs4 | hs4
          · -- n < 300899280
            rcases Nat.lt_or_ge n 300719424 with hs5 | hs5
            · -- n < 300719424
              exact Brocard.berndt_galway_chunk_1672 n m (by omega) (by omega) h
            · -- n >= 300719424
              exact Brocard.berndt_galway_chunk_1673 n m (by omega) (by omega) h
          · -- n >= 300899280
            exact Brocard.berndt_galway_chunk_1674 n m (by omega) (by omega) h
      · -- n >= 301079136
        rcases Nat.lt_or_ge n 301618705 with hs3 | hs3
        · -- n < 301618705
          rcases Nat.lt_or_ge n 301438848 with hs4 | hs4
          · -- n < 301438848
            rcases Nat.lt_or_ge n 301258992 with hs5 | hs5
            · -- n < 301258992
              exact Brocard.berndt_galway_chunk_1675 n m (by omega) (by omega) h
            · -- n >= 301258992
              exact Brocard.berndt_galway_chunk_1676 n m (by omega) (by omega) h
          · -- n >= 301438848
            exact Brocard.berndt_galway_chunk_1677 n m (by omega) (by omega) h
        · -- n >= 301618705
          rcases Nat.lt_or_ge n 301978417 with hs4 | hs4
          · -- n < 301978417
            rcases Nat.lt_or_ge n 301798561 with hs5 | hs5
            · -- n < 301798561
              exact Brocard.berndt_galway_chunk_1678 n m (by omega) (by omega) h
            · -- n >= 301798561
              exact Brocard.berndt_galway_chunk_1679 n m (by omega) (by omega) h
          · -- n >= 301978417
            exact Brocard.berndt_galway_chunk_1680 n m (by omega) (by omega) h
    · -- n >= 302158273
      rcases Nat.lt_or_ge n 303237410 with hs2 | hs2
      · -- n < 303237410
        rcases Nat.lt_or_ge n 302697841 with hs3 | hs3
        · -- n < 302697841
          rcases Nat.lt_or_ge n 302517985 with hs4 | hs4
          · -- n < 302517985
            rcases Nat.lt_or_ge n 302338129 with hs5 | hs5
            · -- n < 302338129
              exact Brocard.berndt_galway_chunk_1681 n m (by omega) (by omega) h
            · -- n >= 302338129
              exact Brocard.berndt_galway_chunk_1682 n m (by omega) (by omega) h
          · -- n >= 302517985
            exact Brocard.berndt_galway_chunk_1683 n m (by omega) (by omega) h
        · -- n >= 302697841
          rcases Nat.lt_or_ge n 303057553 with hs4 | hs4
          · -- n < 303057553
            rcases Nat.lt_or_ge n 302877697 with hs5 | hs5
            · -- n < 302877697
              exact Brocard.berndt_galway_chunk_1684 n m (by omega) (by omega) h
            · -- n >= 302877697
              exact Brocard.berndt_galway_chunk_1685 n m (by omega) (by omega) h
          · -- n >= 303057553
            exact Brocard.berndt_galway_chunk_1686 n m (by omega) (by omega) h
      · -- n >= 303237410
        rcases Nat.lt_or_ge n 303776978 with hs3 | hs3
        · -- n < 303776978
          rcases Nat.lt_or_ge n 303597122 with hs4 | hs4
          · -- n < 303597122
            rcases Nat.lt_or_ge n 303417266 with hs5 | hs5
            · -- n < 303417266
              exact Brocard.berndt_galway_chunk_1687 n m (by omega) (by omega) h
            · -- n >= 303417266
              exact Brocard.berndt_galway_chunk_1688 n m (by omega) (by omega) h
          · -- n >= 303597122
            exact Brocard.berndt_galway_chunk_1689 n m (by omega) (by omega) h
        · -- n >= 303776978
          rcases Nat.lt_or_ge n 304136690 with hs4 | hs4
          · -- n < 304136690
            rcases Nat.lt_or_ge n 303956834 with hs5 | hs5
            · -- n < 303956834
              exact Brocard.berndt_galway_chunk_1690 n m (by omega) (by omega) h
            · -- n >= 303956834
              exact Brocard.berndt_galway_chunk_1691 n m (by omega) (by omega) h
          · -- n >= 304136690
            exact Brocard.berndt_galway_chunk_1692 n m (by omega) (by omega) h
  · -- n >= 304316546
    rcases Nat.lt_or_ge n 306474820 with hs1 | hs1
    · -- n < 306474820
      rcases Nat.lt_or_ge n 305395683 with hs2 | hs2
      · -- n < 305395683
        rcases Nat.lt_or_ge n 304856115 with hs3 | hs3
        · -- n < 304856115
          rcases Nat.lt_or_ge n 304676258 with hs4 | hs4
          · -- n < 304676258
            rcases Nat.lt_or_ge n 304496402 with hs5 | hs5
            · -- n < 304496402
              exact Brocard.berndt_galway_chunk_1693 n m (by omega) (by omega) h
            · -- n >= 304496402
              exact Brocard.berndt_galway_chunk_1694 n m (by omega) (by omega) h
          · -- n >= 304676258
            exact Brocard.berndt_galway_chunk_1695 n m (by omega) (by omega) h
        · -- n >= 304856115
          rcases Nat.lt_or_ge n 305215827 with hs4 | hs4
          · -- n < 305215827
            rcases Nat.lt_or_ge n 305035971 with hs5 | hs5
            · -- n < 305035971
              exact Brocard.berndt_galway_chunk_1696 n m (by omega) (by omega) h
            · -- n >= 305035971
              exact Brocard.berndt_galway_chunk_1697 n m (by omega) (by omega) h
          · -- n >= 305215827
            exact Brocard.berndt_galway_chunk_1698 n m (by omega) (by omega) h
      · -- n >= 305395683
        rcases Nat.lt_or_ge n 305935251 with hs3 | hs3
        · -- n < 305935251
          rcases Nat.lt_or_ge n 305755395 with hs4 | hs4
          · -- n < 305755395
            rcases Nat.lt_or_ge n 305575539 with hs5 | hs5
            · -- n < 305575539
              exact Brocard.berndt_galway_chunk_1699 n m (by omega) (by omega) h
            · -- n >= 305575539
              exact Brocard.berndt_galway_chunk_1700 n m (by omega) (by omega) h
          · -- n >= 305755395
            exact Brocard.berndt_galway_chunk_1701 n m (by omega) (by omega) h
        · -- n >= 305935251
          rcases Nat.lt_or_ge n 306294964 with hs4 | hs4
          · -- n < 306294964
            rcases Nat.lt_or_ge n 306115107 with hs5 | hs5
            · -- n < 306115107
              exact Brocard.berndt_galway_chunk_1702 n m (by omega) (by omega) h
            · -- n >= 306115107
              exact Brocard.berndt_galway_chunk_1703 n m (by omega) (by omega) h
          · -- n >= 306294964
            exact Brocard.berndt_galway_chunk_1704 n m (by omega) (by omega) h
    · -- n >= 306474820
      rcases Nat.lt_or_ge n 307553956 with hs2 | hs2
      · -- n < 307553956
        rcases Nat.lt_or_ge n 307014388 with hs3 | hs3
        · -- n < 307014388
          rcases Nat.lt_or_ge n 306834532 with hs4 | hs4
          · -- n < 306834532
            rcases Nat.lt_or_ge n 306654676 with hs5 | hs5
            · -- n < 306654676
              exact Brocard.berndt_galway_chunk_1705 n m (by omega) (by omega) h
            · -- n >= 306654676
              exact Brocard.berndt_galway_chunk_1706 n m (by omega) (by omega) h
          · -- n >= 306834532
            exact Brocard.berndt_galway_chunk_1707 n m (by omega) (by omega) h
        · -- n >= 307014388
          rcases Nat.lt_or_ge n 307374100 with hs4 | hs4
          · -- n < 307374100
            rcases Nat.lt_or_ge n 307194244 with hs5 | hs5
            · -- n < 307194244
              exact Brocard.berndt_galway_chunk_1708 n m (by omega) (by omega) h
            · -- n >= 307194244
              exact Brocard.berndt_galway_chunk_1709 n m (by omega) (by omega) h
          · -- n >= 307374100
            exact Brocard.berndt_galway_chunk_1710 n m (by omega) (by omega) h
      · -- n >= 307553956
        rcases Nat.lt_or_ge n 308093525 with hs3 | hs3
        · -- n < 308093525
          rcases Nat.lt_or_ge n 307913669 with hs4 | hs4
          · -- n < 307913669
            rcases Nat.lt_or_ge n 307733812 with hs5 | hs5
            · -- n < 307733812
              exact Brocard.berndt_galway_chunk_1711 n m (by omega) (by omega) h
            · -- n >= 307733812
              exact Brocard.berndt_galway_chunk_1712 n m (by omega) (by omega) h
          · -- n >= 307913669
            exact Brocard.berndt_galway_chunk_1713 n m (by omega) (by omega) h
        · -- n >= 308093525
          rcases Nat.lt_or_ge n 308273381 with hs4 | hs4
          · -- n < 308273381
            exact Brocard.berndt_galway_chunk_1714 n m (by omega) (by omega) h
          · -- n >= 308273381
            exact Brocard.berndt_galway_chunk_1715 n m (by omega) (by omega) h

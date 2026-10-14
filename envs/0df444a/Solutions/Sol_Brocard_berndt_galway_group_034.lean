-- Prove2me | solution 1 for Brocard.berndt_galway_group_034
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:05:39.054577+00:00
-- url     : https://prove2.me/submissions/a433302b-cd06-4e0e-800d-b0f7a1e92fe3

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1531
import Theorems.Thm_Brocard_berndt_galway_chunk_1532
import Theorems.Thm_Brocard_berndt_galway_chunk_1533
import Theorems.Thm_Brocard_berndt_galway_chunk_1534
import Theorems.Thm_Brocard_berndt_galway_chunk_1535
import Theorems.Thm_Brocard_berndt_galway_chunk_1536
import Theorems.Thm_Brocard_berndt_galway_chunk_1537
import Theorems.Thm_Brocard_berndt_galway_chunk_1538
import Theorems.Thm_Brocard_berndt_galway_chunk_1539
import Theorems.Thm_Brocard_berndt_galway_chunk_1540
import Theorems.Thm_Brocard_berndt_galway_chunk_1541
import Theorems.Thm_Brocard_berndt_galway_chunk_1542
import Theorems.Thm_Brocard_berndt_galway_chunk_1543
import Theorems.Thm_Brocard_berndt_galway_chunk_1544
import Theorems.Thm_Brocard_berndt_galway_chunk_1545
import Theorems.Thm_Brocard_berndt_galway_chunk_1546
import Theorems.Thm_Brocard_berndt_galway_chunk_1547
import Theorems.Thm_Brocard_berndt_galway_chunk_1548
import Theorems.Thm_Brocard_berndt_galway_chunk_1549
import Theorems.Thm_Brocard_berndt_galway_chunk_1550
import Theorems.Thm_Brocard_berndt_galway_chunk_1551
import Theorems.Thm_Brocard_berndt_galway_chunk_1552
import Theorems.Thm_Brocard_berndt_galway_chunk_1553
import Theorems.Thm_Brocard_berndt_galway_chunk_1554
import Theorems.Thm_Brocard_berndt_galway_chunk_1555
import Theorems.Thm_Brocard_berndt_galway_chunk_1556
import Theorems.Thm_Brocard_berndt_galway_chunk_1557
import Theorems.Thm_Brocard_berndt_galway_chunk_1558
import Theorems.Thm_Brocard_berndt_galway_chunk_1559
import Theorems.Thm_Brocard_berndt_galway_chunk_1560
import Theorems.Thm_Brocard_berndt_galway_chunk_1561
import Theorems.Thm_Brocard_berndt_galway_chunk_1562
import Theorems.Thm_Brocard_berndt_galway_chunk_1563
import Theorems.Thm_Brocard_berndt_galway_chunk_1564
import Theorems.Thm_Brocard_berndt_galway_chunk_1565
import Theorems.Thm_Brocard_berndt_galway_chunk_1566
import Theorems.Thm_Brocard_berndt_galway_chunk_1567
import Theorems.Thm_Brocard_berndt_galway_chunk_1568
import Theorems.Thm_Brocard_berndt_galway_chunk_1569
import Theorems.Thm_Brocard_berndt_galway_chunk_1570
import Theorems.Thm_Brocard_berndt_galway_chunk_1571
import Theorems.Thm_Brocard_berndt_galway_chunk_1572
import Theorems.Thm_Brocard_berndt_galway_chunk_1573
import Theorems.Thm_Brocard_berndt_galway_chunk_1574
import Theorems.Thm_Brocard_berndt_galway_chunk_1575
import Theorems.Thm_Brocard_berndt_galway_chunk_1576

theorem solution (n m : ℕ) (h1 : 275179856 ≤ n) (h2 : n < 283453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 279316546 with hs0 | hs0
  · -- n < 279316546
    rcases Nat.lt_or_ge n 277338129 with hs1 | hs1
    · -- n < 277338129
      rcases Nat.lt_or_ge n 276258992 with hs2 | hs2
      · -- n < 276258992
        rcases Nat.lt_or_ge n 275719424 with hs3 | hs3
        · -- n < 275719424
          rcases Nat.lt_or_ge n 275539568 with hs4 | hs4
          · -- n < 275539568
            rcases Nat.lt_or_ge n 275359712 with hs5 | hs5
            · -- n < 275359712
              exact Brocard.berndt_galway_chunk_1531 n m (by omega) (by omega) h
            · -- n >= 275359712
              exact Brocard.berndt_galway_chunk_1532 n m (by omega) (by omega) h
          · -- n >= 275539568
            exact Brocard.berndt_galway_chunk_1533 n m (by omega) (by omega) h
        · -- n >= 275719424
          rcases Nat.lt_or_ge n 276079136 with hs4 | hs4
          · -- n < 276079136
            rcases Nat.lt_or_ge n 275899280 with hs5 | hs5
            · -- n < 275899280
              exact Brocard.berndt_galway_chunk_1534 n m (by omega) (by omega) h
            · -- n >= 275899280
              exact Brocard.berndt_galway_chunk_1535 n m (by omega) (by omega) h
          · -- n >= 276079136
            exact Brocard.berndt_galway_chunk_1536 n m (by omega) (by omega) h
      · -- n >= 276258992
        rcases Nat.lt_or_ge n 276798561 with hs3 | hs3
        · -- n < 276798561
          rcases Nat.lt_or_ge n 276618705 with hs4 | hs4
          · -- n < 276618705
            rcases Nat.lt_or_ge n 276438848 with hs5 | hs5
            · -- n < 276438848
              exact Brocard.berndt_galway_chunk_1537 n m (by omega) (by omega) h
            · -- n >= 276438848
              exact Brocard.berndt_galway_chunk_1538 n m (by omega) (by omega) h
          · -- n >= 276618705
            exact Brocard.berndt_galway_chunk_1539 n m (by omega) (by omega) h
        · -- n >= 276798561
          rcases Nat.lt_or_ge n 277158273 with hs4 | hs4
          · -- n < 277158273
            rcases Nat.lt_or_ge n 276978417 with hs5 | hs5
            · -- n < 276978417
              exact Brocard.berndt_galway_chunk_1540 n m (by omega) (by omega) h
            · -- n >= 276978417
              exact Brocard.berndt_galway_chunk_1541 n m (by omega) (by omega) h
          · -- n >= 277158273
            exact Brocard.berndt_galway_chunk_1542 n m (by omega) (by omega) h
    · -- n >= 277338129
      rcases Nat.lt_or_ge n 278417266 with hs2 | hs2
      · -- n < 278417266
        rcases Nat.lt_or_ge n 277877697 with hs3 | hs3
        · -- n < 277877697
          rcases Nat.lt_or_ge n 277697841 with hs4 | hs4
          · -- n < 277697841
            rcases Nat.lt_or_ge n 277517985 with hs5 | hs5
            · -- n < 277517985
              exact Brocard.berndt_galway_chunk_1543 n m (by omega) (by omega) h
            · -- n >= 277517985
              exact Brocard.berndt_galway_chunk_1544 n m (by omega) (by omega) h
          · -- n >= 277697841
            exact Brocard.berndt_galway_chunk_1545 n m (by omega) (by omega) h
        · -- n >= 277877697
          rcases Nat.lt_or_ge n 278237410 with hs4 | hs4
          · -- n < 278237410
            rcases Nat.lt_or_ge n 278057553 with hs5 | hs5
            · -- n < 278057553
              exact Brocard.berndt_galway_chunk_1546 n m (by omega) (by omega) h
            · -- n >= 278057553
              exact Brocard.berndt_galway_chunk_1547 n m (by omega) (by omega) h
          · -- n >= 278237410
            exact Brocard.berndt_galway_chunk_1548 n m (by omega) (by omega) h
      · -- n >= 278417266
        rcases Nat.lt_or_ge n 278956834 with hs3 | hs3
        · -- n < 278956834
          rcases Nat.lt_or_ge n 278776978 with hs4 | hs4
          · -- n < 278776978
            rcases Nat.lt_or_ge n 278597122 with hs5 | hs5
            · -- n < 278597122
              exact Brocard.berndt_galway_chunk_1549 n m (by omega) (by omega) h
            · -- n >= 278597122
              exact Brocard.berndt_galway_chunk_1550 n m (by omega) (by omega) h
          · -- n >= 278776978
            exact Brocard.berndt_galway_chunk_1551 n m (by omega) (by omega) h
        · -- n >= 278956834
          rcases Nat.lt_or_ge n 279136690 with hs4 | hs4
          · -- n < 279136690
            exact Brocard.berndt_galway_chunk_1552 n m (by omega) (by omega) h
          · -- n >= 279136690
            exact Brocard.berndt_galway_chunk_1553 n m (by omega) (by omega) h
  · -- n >= 279316546
    rcases Nat.lt_or_ge n 281474820 with hs1 | hs1
    · -- n < 281474820
      rcases Nat.lt_or_ge n 280395683 with hs2 | hs2
      · -- n < 280395683
        rcases Nat.lt_or_ge n 279856115 with hs3 | hs3
        · -- n < 279856115
          rcases Nat.lt_or_ge n 279676258 with hs4 | hs4
          · -- n < 279676258
            rcases Nat.lt_or_ge n 279496402 with hs5 | hs5
            · -- n < 279496402
              exact Brocard.berndt_galway_chunk_1554 n m (by omega) (by omega) h
            · -- n >= 279496402
              exact Brocard.berndt_galway_chunk_1555 n m (by omega) (by omega) h
          · -- n >= 279676258
            exact Brocard.berndt_galway_chunk_1556 n m (by omega) (by omega) h
        · -- n >= 279856115
          rcases Nat.lt_or_ge n 280215827 with hs4 | hs4
          · -- n < 280215827
            rcases Nat.lt_or_ge n 280035971 with hs5 | hs5
            · -- n < 280035971
              exact Brocard.berndt_galway_chunk_1557 n m (by omega) (by omega) h
            · -- n >= 280035971
              exact Brocard.berndt_galway_chunk_1558 n m (by omega) (by omega) h
          · -- n >= 280215827
            exact Brocard.berndt_galway_chunk_1559 n m (by omega) (by omega) h
      · -- n >= 280395683
        rcases Nat.lt_or_ge n 280935251 with hs3 | hs3
        · -- n < 280935251
          rcases Nat.lt_or_ge n 280755395 with hs4 | hs4
          · -- n < 280755395
            rcases Nat.lt_or_ge n 280575539 with hs5 | hs5
            · -- n < 280575539
              exact Brocard.berndt_galway_chunk_1560 n m (by omega) (by omega) h
            · -- n >= 280575539
              exact Brocard.berndt_galway_chunk_1561 n m (by omega) (by omega) h
          · -- n >= 280755395
            exact Brocard.berndt_galway_chunk_1562 n m (by omega) (by omega) h
        · -- n >= 280935251
          rcases Nat.lt_or_ge n 281294964 with hs4 | hs4
          · -- n < 281294964
            rcases Nat.lt_or_ge n 281115107 with hs5 | hs5
            · -- n < 281115107
              exact Brocard.berndt_galway_chunk_1563 n m (by omega) (by omega) h
            · -- n >= 281115107
              exact Brocard.berndt_galway_chunk_1564 n m (by omega) (by omega) h
          · -- n >= 281294964
            exact Brocard.berndt_galway_chunk_1565 n m (by omega) (by omega) h
    · -- n >= 281474820
      rcases Nat.lt_or_ge n 282553956 with hs2 | hs2
      · -- n < 282553956
        rcases Nat.lt_or_ge n 282014388 with hs3 | hs3
        · -- n < 282014388
          rcases Nat.lt_or_ge n 281834532 with hs4 | hs4
          · -- n < 281834532
            rcases Nat.lt_or_ge n 281654676 with hs5 | hs5
            · -- n < 281654676
              exact Brocard.berndt_galway_chunk_1566 n m (by omega) (by omega) h
            · -- n >= 281654676
              exact Brocard.berndt_galway_chunk_1567 n m (by omega) (by omega) h
          · -- n >= 281834532
            exact Brocard.berndt_galway_chunk_1568 n m (by omega) (by omega) h
        · -- n >= 282014388
          rcases Nat.lt_or_ge n 282374100 with hs4 | hs4
          · -- n < 282374100
            rcases Nat.lt_or_ge n 282194244 with hs5 | hs5
            · -- n < 282194244
              exact Brocard.berndt_galway_chunk_1569 n m (by omega) (by omega) h
            · -- n >= 282194244
              exact Brocard.berndt_galway_chunk_1570 n m (by omega) (by omega) h
          · -- n >= 282374100
            exact Brocard.berndt_galway_chunk_1571 n m (by omega) (by omega) h
      · -- n >= 282553956
        rcases Nat.lt_or_ge n 283093525 with hs3 | hs3
        · -- n < 283093525
          rcases Nat.lt_or_ge n 282913669 with hs4 | hs4
          · -- n < 282913669
            rcases Nat.lt_or_ge n 282733812 with hs5 | hs5
            · -- n < 282733812
              exact Brocard.berndt_galway_chunk_1572 n m (by omega) (by omega) h
            · -- n >= 282733812
              exact Brocard.berndt_galway_chunk_1573 n m (by omega) (by omega) h
          · -- n >= 282913669
            exact Brocard.berndt_galway_chunk_1574 n m (by omega) (by omega) h
        · -- n >= 283093525
          rcases Nat.lt_or_ge n 283273381 with hs4 | hs4
          · -- n < 283273381
            exact Brocard.berndt_galway_chunk_1575 n m (by omega) (by omega) h
          · -- n >= 283273381
            exact Brocard.berndt_galway_chunk_1576 n m (by omega) (by omega) h

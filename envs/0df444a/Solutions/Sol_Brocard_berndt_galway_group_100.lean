-- Prove2me | solution 1 for Brocard.berndt_galway_group_100
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:27:30.949385+00:00
-- url     : https://prove2.me/submissions/7f53bfa5-44a8-4750-8b69-44e085eeed1d

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4590
import Theorems.Thm_Brocard_berndt_galway_chunk_4591
import Theorems.Thm_Brocard_berndt_galway_chunk_4592
import Theorems.Thm_Brocard_berndt_galway_chunk_4593
import Theorems.Thm_Brocard_berndt_galway_chunk_4594
import Theorems.Thm_Brocard_berndt_galway_chunk_4595
import Theorems.Thm_Brocard_berndt_galway_chunk_4596
import Theorems.Thm_Brocard_berndt_galway_chunk_4597
import Theorems.Thm_Brocard_berndt_galway_chunk_4598
import Theorems.Thm_Brocard_berndt_galway_chunk_4599
import Theorems.Thm_Brocard_berndt_galway_chunk_4600
import Theorems.Thm_Brocard_berndt_galway_chunk_4601
import Theorems.Thm_Brocard_berndt_galway_chunk_4602
import Theorems.Thm_Brocard_berndt_galway_chunk_4603
import Theorems.Thm_Brocard_berndt_galway_chunk_4604
import Theorems.Thm_Brocard_berndt_galway_chunk_4605
import Theorems.Thm_Brocard_berndt_galway_chunk_4606
import Theorems.Thm_Brocard_berndt_galway_chunk_4607
import Theorems.Thm_Brocard_berndt_galway_chunk_4608
import Theorems.Thm_Brocard_berndt_galway_chunk_4609
import Theorems.Thm_Brocard_berndt_galway_chunk_4610
import Theorems.Thm_Brocard_berndt_galway_chunk_4611
import Theorems.Thm_Brocard_berndt_galway_chunk_4612
import Theorems.Thm_Brocard_berndt_galway_chunk_4613
import Theorems.Thm_Brocard_berndt_galway_chunk_4614
import Theorems.Thm_Brocard_berndt_galway_chunk_4615
import Theorems.Thm_Brocard_berndt_galway_chunk_4616
import Theorems.Thm_Brocard_berndt_galway_chunk_4617
import Theorems.Thm_Brocard_berndt_galway_chunk_4618
import Theorems.Thm_Brocard_berndt_galway_chunk_4619
import Theorems.Thm_Brocard_berndt_galway_chunk_4620
import Theorems.Thm_Brocard_berndt_galway_chunk_4621
import Theorems.Thm_Brocard_berndt_galway_chunk_4622
import Theorems.Thm_Brocard_berndt_galway_chunk_4623
import Theorems.Thm_Brocard_berndt_galway_chunk_4624
import Theorems.Thm_Brocard_berndt_galway_chunk_4625
import Theorems.Thm_Brocard_berndt_galway_chunk_4626
import Theorems.Thm_Brocard_berndt_galway_chunk_4627
import Theorems.Thm_Brocard_berndt_galway_chunk_4628
import Theorems.Thm_Brocard_berndt_galway_chunk_4629
import Theorems.Thm_Brocard_berndt_galway_chunk_4630
import Theorems.Thm_Brocard_berndt_galway_chunk_4631
import Theorems.Thm_Brocard_berndt_galway_chunk_4632
import Theorems.Thm_Brocard_berndt_galway_chunk_4633
import Theorems.Thm_Brocard_berndt_galway_chunk_4634
import Theorems.Thm_Brocard_berndt_galway_chunk_4635
import Theorems.Thm_Brocard_berndt_galway_chunk_4636

theorem solution (n m : ℕ) (h1 : 825359712 ≤ n) (h2 : n < 833812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 829676258 with hs0 | hs0
  · -- n < 829676258
    rcases Nat.lt_or_ge n 827517985 with hs1 | hs1
    · -- n < 827517985
      rcases Nat.lt_or_ge n 826438848 with hs2 | hs2
      · -- n < 826438848
        rcases Nat.lt_or_ge n 825899280 with hs3 | hs3
        · -- n < 825899280
          rcases Nat.lt_or_ge n 825719424 with hs4 | hs4
          · -- n < 825719424
            rcases Nat.lt_or_ge n 825539568 with hs5 | hs5
            · -- n < 825539568
              exact Brocard.berndt_galway_chunk_4590 n m (by omega) (by omega) h
            · -- n >= 825539568
              exact Brocard.berndt_galway_chunk_4591 n m (by omega) (by omega) h
          · -- n >= 825719424
            exact Brocard.berndt_galway_chunk_4592 n m (by omega) (by omega) h
        · -- n >= 825899280
          rcases Nat.lt_or_ge n 826258992 with hs4 | hs4
          · -- n < 826258992
            rcases Nat.lt_or_ge n 826079136 with hs5 | hs5
            · -- n < 826079136
              exact Brocard.berndt_galway_chunk_4593 n m (by omega) (by omega) h
            · -- n >= 826079136
              exact Brocard.berndt_galway_chunk_4594 n m (by omega) (by omega) h
          · -- n >= 826258992
            exact Brocard.berndt_galway_chunk_4595 n m (by omega) (by omega) h
      · -- n >= 826438848
        rcases Nat.lt_or_ge n 826978417 with hs3 | hs3
        · -- n < 826978417
          rcases Nat.lt_or_ge n 826798561 with hs4 | hs4
          · -- n < 826798561
            rcases Nat.lt_or_ge n 826618705 with hs5 | hs5
            · -- n < 826618705
              exact Brocard.berndt_galway_chunk_4596 n m (by omega) (by omega) h
            · -- n >= 826618705
              exact Brocard.berndt_galway_chunk_4597 n m (by omega) (by omega) h
          · -- n >= 826798561
            exact Brocard.berndt_galway_chunk_4598 n m (by omega) (by omega) h
        · -- n >= 826978417
          rcases Nat.lt_or_ge n 827338129 with hs4 | hs4
          · -- n < 827338129
            rcases Nat.lt_or_ge n 827158273 with hs5 | hs5
            · -- n < 827158273
              exact Brocard.berndt_galway_chunk_4599 n m (by omega) (by omega) h
            · -- n >= 827158273
              exact Brocard.berndt_galway_chunk_4600 n m (by omega) (by omega) h
          · -- n >= 827338129
            exact Brocard.berndt_galway_chunk_4601 n m (by omega) (by omega) h
    · -- n >= 827517985
      rcases Nat.lt_or_ge n 828597122 with hs2 | hs2
      · -- n < 828597122
        rcases Nat.lt_or_ge n 828057553 with hs3 | hs3
        · -- n < 828057553
          rcases Nat.lt_or_ge n 827877697 with hs4 | hs4
          · -- n < 827877697
            rcases Nat.lt_or_ge n 827697841 with hs5 | hs5
            · -- n < 827697841
              exact Brocard.berndt_galway_chunk_4602 n m (by omega) (by omega) h
            · -- n >= 827697841
              exact Brocard.berndt_galway_chunk_4603 n m (by omega) (by omega) h
          · -- n >= 827877697
            exact Brocard.berndt_galway_chunk_4604 n m (by omega) (by omega) h
        · -- n >= 828057553
          rcases Nat.lt_or_ge n 828417266 with hs4 | hs4
          · -- n < 828417266
            rcases Nat.lt_or_ge n 828237410 with hs5 | hs5
            · -- n < 828237410
              exact Brocard.berndt_galway_chunk_4605 n m (by omega) (by omega) h
            · -- n >= 828237410
              exact Brocard.berndt_galway_chunk_4606 n m (by omega) (by omega) h
          · -- n >= 828417266
            exact Brocard.berndt_galway_chunk_4607 n m (by omega) (by omega) h
      · -- n >= 828597122
        rcases Nat.lt_or_ge n 829136690 with hs3 | hs3
        · -- n < 829136690
          rcases Nat.lt_or_ge n 828956834 with hs4 | hs4
          · -- n < 828956834
            rcases Nat.lt_or_ge n 828776978 with hs5 | hs5
            · -- n < 828776978
              exact Brocard.berndt_galway_chunk_4608 n m (by omega) (by omega) h
            · -- n >= 828776978
              exact Brocard.berndt_galway_chunk_4609 n m (by omega) (by omega) h
          · -- n >= 828956834
            exact Brocard.berndt_galway_chunk_4610 n m (by omega) (by omega) h
        · -- n >= 829136690
          rcases Nat.lt_or_ge n 829496402 with hs4 | hs4
          · -- n < 829496402
            rcases Nat.lt_or_ge n 829316546 with hs5 | hs5
            · -- n < 829316546
              exact Brocard.berndt_galway_chunk_4611 n m (by omega) (by omega) h
            · -- n >= 829316546
              exact Brocard.berndt_galway_chunk_4612 n m (by omega) (by omega) h
          · -- n >= 829496402
            exact Brocard.berndt_galway_chunk_4613 n m (by omega) (by omega) h
  · -- n >= 829676258
    rcases Nat.lt_or_ge n 831834532 with hs1 | hs1
    · -- n < 831834532
      rcases Nat.lt_or_ge n 830755395 with hs2 | hs2
      · -- n < 830755395
        rcases Nat.lt_or_ge n 830215827 with hs3 | hs3
        · -- n < 830215827
          rcases Nat.lt_or_ge n 830035971 with hs4 | hs4
          · -- n < 830035971
            rcases Nat.lt_or_ge n 829856115 with hs5 | hs5
            · -- n < 829856115
              exact Brocard.berndt_galway_chunk_4614 n m (by omega) (by omega) h
            · -- n >= 829856115
              exact Brocard.berndt_galway_chunk_4615 n m (by omega) (by omega) h
          · -- n >= 830035971
            exact Brocard.berndt_galway_chunk_4616 n m (by omega) (by omega) h
        · -- n >= 830215827
          rcases Nat.lt_or_ge n 830575539 with hs4 | hs4
          · -- n < 830575539
            rcases Nat.lt_or_ge n 830395683 with hs5 | hs5
            · -- n < 830395683
              exact Brocard.berndt_galway_chunk_4617 n m (by omega) (by omega) h
            · -- n >= 830395683
              exact Brocard.berndt_galway_chunk_4618 n m (by omega) (by omega) h
          · -- n >= 830575539
            exact Brocard.berndt_galway_chunk_4619 n m (by omega) (by omega) h
      · -- n >= 830755395
        rcases Nat.lt_or_ge n 831294964 with hs3 | hs3
        · -- n < 831294964
          rcases Nat.lt_or_ge n 831115107 with hs4 | hs4
          · -- n < 831115107
            rcases Nat.lt_or_ge n 830935251 with hs5 | hs5
            · -- n < 830935251
              exact Brocard.berndt_galway_chunk_4620 n m (by omega) (by omega) h
            · -- n >= 830935251
              exact Brocard.berndt_galway_chunk_4621 n m (by omega) (by omega) h
          · -- n >= 831115107
            exact Brocard.berndt_galway_chunk_4622 n m (by omega) (by omega) h
        · -- n >= 831294964
          rcases Nat.lt_or_ge n 831654676 with hs4 | hs4
          · -- n < 831654676
            rcases Nat.lt_or_ge n 831474820 with hs5 | hs5
            · -- n < 831474820
              exact Brocard.berndt_galway_chunk_4623 n m (by omega) (by omega) h
            · -- n >= 831474820
              exact Brocard.berndt_galway_chunk_4624 n m (by omega) (by omega) h
          · -- n >= 831654676
            exact Brocard.berndt_galway_chunk_4625 n m (by omega) (by omega) h
    · -- n >= 831834532
      rcases Nat.lt_or_ge n 832913669 with hs2 | hs2
      · -- n < 832913669
        rcases Nat.lt_or_ge n 832374100 with hs3 | hs3
        · -- n < 832374100
          rcases Nat.lt_or_ge n 832194244 with hs4 | hs4
          · -- n < 832194244
            rcases Nat.lt_or_ge n 832014388 with hs5 | hs5
            · -- n < 832014388
              exact Brocard.berndt_galway_chunk_4626 n m (by omega) (by omega) h
            · -- n >= 832014388
              exact Brocard.berndt_galway_chunk_4627 n m (by omega) (by omega) h
          · -- n >= 832194244
            exact Brocard.berndt_galway_chunk_4628 n m (by omega) (by omega) h
        · -- n >= 832374100
          rcases Nat.lt_or_ge n 832733812 with hs4 | hs4
          · -- n < 832733812
            rcases Nat.lt_or_ge n 832553956 with hs5 | hs5
            · -- n < 832553956
              exact Brocard.berndt_galway_chunk_4629 n m (by omega) (by omega) h
            · -- n >= 832553956
              exact Brocard.berndt_galway_chunk_4630 n m (by omega) (by omega) h
          · -- n >= 832733812
            exact Brocard.berndt_galway_chunk_4631 n m (by omega) (by omega) h
      · -- n >= 832913669
        rcases Nat.lt_or_ge n 833453237 with hs3 | hs3
        · -- n < 833453237
          rcases Nat.lt_or_ge n 833273381 with hs4 | hs4
          · -- n < 833273381
            rcases Nat.lt_or_ge n 833093525 with hs5 | hs5
            · -- n < 833093525
              exact Brocard.berndt_galway_chunk_4632 n m (by omega) (by omega) h
            · -- n >= 833093525
              exact Brocard.berndt_galway_chunk_4633 n m (by omega) (by omega) h
          · -- n >= 833273381
            exact Brocard.berndt_galway_chunk_4634 n m (by omega) (by omega) h
        · -- n >= 833453237
          rcases Nat.lt_or_ge n 833633093 with hs4 | hs4
          · -- n < 833633093
            exact Brocard.berndt_galway_chunk_4635 n m (by omega) (by omega) h
          · -- n >= 833633093
            exact Brocard.berndt_galway_chunk_4636 n m (by omega) (by omega) h

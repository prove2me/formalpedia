-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleThree.PS_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:31:39.017119+00:00
-- url     : https://prove2.me/submissions/9205e70b-7d2f-4bd2-a4cb-face5be981b2

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_max_price_val

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)
namespace FairSelling.EqualProceedsExampleThree
theorem _root_.solution : PS (N + 1) (val N) (price N) = 1 := by
  unfold PS
  rw [Finset.sum_congr rfl fun g _ => max_price_val N g, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (by positivity)
end FairSelling.EqualProceedsExampleThree

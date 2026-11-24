-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleFour.outSellAll_equalProceeds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:32:11.358815+00:00
-- url     : https://prove2.me/submissions/2055675e-ca1c-425f-adf7-1d8f970345ac

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
import Theorems.Thm_FairSelling_EqualProceedsExampleFour_price_sum

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)
namespace FairSelling.EqualProceedsExampleFour
theorem _root_.solution : (outSellAll N).EqualProceeds (price N) := by
  intro i
  simp only [outSellAll]
  rw [price_sum, Finset.card_univ, Fintype.card_fin, div_self (by positivity)]
end FairSelling.EqualProceedsExampleFour

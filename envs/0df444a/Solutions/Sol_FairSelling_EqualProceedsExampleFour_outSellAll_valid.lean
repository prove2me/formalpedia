-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleFour.outSellAll_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:32:07.912091+00:00
-- url     : https://prove2.me/submissions/18dd230c-9bc9-4561-acc3-2f67a047f0d6

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
theorem _root_.solution : (outSellAll N).Valid (price N) := by
  refine ⟨fun j => by simp [outSellAll], fun j k _ => by simp [outSellAll], fun j => by
    simp [outSellAll], ?_⟩
  simp only [outSellAll]
  rw [price_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp
end FairSelling.EqualProceedsExampleFour

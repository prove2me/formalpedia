-- Prove2me | solution 1 for FairSelling.SEF1_of_SEFX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:30.236645+00:00
-- url     : https://prove2.me/submissions/df5b9e0f-03ba-4bdf-a09c-e674daaf6a89

import Mathlib
import Definitions.Def_RequestProject_Selling
import Theorems.Thm_FairSelling_vbarSum_nonneg

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution (hv : ∀ i g, 0 ≤ v i g) (hvalid : o.Valid p) (h : SEFX v p o) :
    SEF1 v p o := by
  intro i j
  refine ⟨(h i j).1, fun hj => ?_⟩
  rcases (h i j).2 hj with hEF | hall
  · exact Or.inl hEF
  · rcases Finset.eq_empty_or_nonempty (o.kept j) with hemp | ⟨g, hg⟩
    · refine Or.inl ?_
      have h1 : 0 ≤ vbarSum (v i) p (o.kept i) := vbarSum_nonneg (hv i) _
      have h2 := hvalid.2.2.1 i
      rw [hemp]
      simp only [vbarSum, Finset.sum_empty] at *
      linarith
    · exact Or.inr ⟨g, hg, hall g hg⟩
end FairSelling

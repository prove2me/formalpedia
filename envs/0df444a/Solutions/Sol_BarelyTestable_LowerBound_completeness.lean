-- Prove2me | solution 1 for BarelyTestable.LowerBound.completeness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:34:08.24378+00:00
-- url     : https://prove2.me/submissions/2a2f2146-9155-45fb-8bf4-478cbe257349

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Construction
import Theorems.Thm_BarelyTestable_LowerBound_square_slack

set_option autoImplicit false

open BarelyTestable.LowerBound NonmonotoneSubmod.Shared MeasureTheory

namespace BTHelper_completeness

variable {α : Type} [Fintype α] [DecidableEq α] {f : Oracle α}

omit [Fintype α] in
/-- Nonnegative squares imply diminishing returns (induction on `T \ S`). -/
theorem marginal (hs : NonnegativeSquares f) : DiminishingReturns f := by
  intro S T u hst hu
  have aux (D : Finset α) (hd : u ∉ S ∪ D) :
      f (insert u (S ∪ D)) - f (S ∪ D) ≤ f (insert u S) - f S := by
    induction D using Finset.induction_on with
    | empty => simp
    | @insert a D ha ih =>
      rw [Finset.union_insert] at hd ⊢
      have hu' : u ∉ S ∪ D := by grind
      by_cases ha' : a ∈ S ∪ D
      · simpa [Finset.insert_eq_of_mem ha'] using ih hu'
      · have hx := hs (S ∪ D) u a ⟨by grind, hu', ha'⟩
        unfold slack at hx
        linarith [ih hu']
  simpa [Finset.union_eq_right.mpr hst] using
    aux T (by simpa [Finset.union_eq_right.mpr hst] using hu)

/-- Diminishing returns implies submodularity. -/
theorem global (hd : DiminishingReturns f) : Submodular f := by
  have aux (S T D : Finset α) (hst : S ⊆ T) (hdis : Disjoint D T) :
      f (T ∪ D) - f T ≤ f (S ∪ D) - f S := by
    induction D using Finset.induction_on with
    | empty => simp
    | @insert a D ha ih =>
      rw [Finset.disjoint_insert_left] at hdis
      have h := hd (S ∪ D) (T ∪ D) (u := a) (Finset.union_subset_union_left hst)
        (by simp [hdis.1, ha])
      rw [Finset.union_insert, Finset.union_insert]
      linarith [ih hdis.2]
  intro A B
  have h := aux (A ∩ B) A (B \ A) Finset.inter_subset_left
    (Finset.disjoint_left.mpr (fun x hx h => (Finset.mem_sdiff.mp hx).2 h))
  have h1 : A ∪ (B \ A) = A ∪ B := by ext; simp
  have h2 : (A ∩ B) ∪ (B \ A) = B := by ext; simp; tauto
  rw [h1, h2] at h
  linarith

end BTHelper_completeness

theorem solution {m : ℕ} (hm : 9 ≤ m) (r : Sample m) :
    Submodular (hard r true) := by
  apply BTHelper_completeness.global
  apply BTHelper_completeness.marginal
  intro S u v hv
  have h := BarelyTestable.LowerBound.square_slack hm r true S u v hv
  by_cases hs : Center r.1 r.2.1 (xPart S) (yPart S) ∧
      ((u = actionA ∧ v = actionB) ∨ (u = actionB ∧ v = actionA))
  · rw [h.1 hs]; simp only [if_true]; positivity
  · exact h.2 hs

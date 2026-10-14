-- Prove2me | solution 1 for BalancedPrices.ClosureMax.optVal_mono
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:45:38.536513+00:00
-- url     : https://prove2.me/submissions/e06b2e3d-36ff-48dc-bf7f-5ccf0079e9d5

import Mathlib
import Definitions.Def_BalancedPrices_ClosureMax_Composition
open BalancedPrices.ClosureMax



theorem solution {n : ℕ} {X : Fin n → Type*}
    (Vsp : ∀ i, Set (X i → ℝ))
    (hV : ∀ i (f : X i → ℝ), f ∈ Vsp i → ∀ xi, 0 ≤ f xi ∧ f xi ≤ 1)
    (vt vf : BalancedPrices.Extension.Valuation X) (hvt : ∀ i, vt i ∈ Vsp i)
    (hvf : ∀ i, vf i ∈ VmaxSet Vsp i)
    (hle : ∀ i xi, vt i xi ≤ vf i xi)
    (S : Set (BalancedPrices.Extension.Outcome X)) : BalancedPrices.Extension.optVal vt S ≤ BalancedPrices.Extension.optVal vf S := by
  classical
  by_cases hS : S.Nonempty
  · have hbound : BddAbove (BalancedPrices.Extension.welfare vf '' S) := by
      refine ⟨(n : ℝ), ?_⟩
      rintro z ⟨x, hx, rfl⟩
      unfold BalancedPrices.Extension.welfare
      calc
        (∑ i, vf i (x i)) ≤ ∑ _i : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          obtain ⟨s, hs, hsub, heq⟩ := hvf i
          rw [heq]
          exact Finset.sup'_le hs _ (fun f hf => (hV i f (hsub hf) (x i)).2)
        _ = n := by simp
    apply csSup_le (hS.image _)
    rintro z ⟨x, hx, rfl⟩
    exact (Finset.sum_le_sum (fun i _ => hle i (x i))).trans
      (le_csSup hbound ⟨x, hx, rfl⟩)
  · have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    simp [hempty, BalancedPrices.Extension.optVal]



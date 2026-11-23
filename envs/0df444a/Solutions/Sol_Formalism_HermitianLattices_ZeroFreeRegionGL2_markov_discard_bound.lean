-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.markov_discard_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:47.494981+00:00
-- url     : https://prove2.me/submissions/9edf0160-1fd0-4bce-a26f-88f372380e0d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : MarkovDiscard := by
  intro P B J S V t ht hS hlt
  by_contra hcon
  push Not at hcon
  have hcov : P ⊆ B ∪ (Finset.univ.biUnion fun j => P.filter fun q => t < |S j q|) := by
    intro q hq
    by_cases hB : q ∈ B
    · exact mem_union_left _ hB
    · obtain ⟨j, hj⟩ := hcon q hq hB
      exact mem_union_right _ (mem_biUnion.2 ⟨j, mem_univ _, mem_filter.2 ⟨hq, hj⟩⟩)
  have hj : ∀ j, (((P.filter fun q => t < |S j q|).card : ℕ) : ℝ) ≤ V / t ^ 2 * P.card := by
    intro j
    have h1 : (((P.filter fun q => t < |S j q|).card : ℕ) : ℝ) * t ^ 2 ≤ ∑ q ∈ P, S j q ^ 2 := by
      calc (((P.filter fun q => t < |S j q|).card : ℕ) : ℝ) * t ^ 2
          = ∑ q ∈ P.filter (fun q => t < |S j q|), t ^ 2 := by simp
        _ ≤ ∑ q ∈ P.filter (fun q => t < |S j q|), S j q ^ 2 := by
            apply Finset.sum_le_sum
            intro q hq
            have := (mem_filter.1 hq).2
            rw [← sq_abs (S j q)]
            exact pow_le_pow_left₀ ht.le this.le 2
        _ ≤ ∑ q ∈ P, S j q ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
    have h2 := h1.trans (hS j)
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact h2
  have hc : (P.card : ℝ) ≤ B.card + ∑ j : Fin J, (((P.filter fun q => t < |S j q|).card : ℕ) : ℝ) := by
    have := (Finset.card_le_card hcov).trans ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
    exact_mod_cast this
  have : ∑ j : Fin J, (((P.filter fun q => t < |S j q|).card : ℕ) : ℝ) ≤ J * (V / t ^ 2 * P.card) := by
    calc _ ≤ ∑ _j : Fin J, V / t ^ 2 * P.card := Finset.sum_le_sum fun j _ => hj j
      _ = _ := by simp
  nlinarith
end Formalism.HermitianLattices.ZeroFreeRegionGL2

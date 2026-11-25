-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.logBinomialDeficit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:50:43.788022+00:00
-- url     : https://prove2.me/submissions/17fb664e-87ce-4dd0-8f1d-2176fb6cc530

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogBinomialProperties
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__nonneg_28215f1bee0c
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__lower2_d91edae1b020
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__half_e845f6006a1c
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_fT_concave
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_abel_tails

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution : LogBinomialDeficit := by
  intro k' L al Bs hk hal hBs h4 hDe
  have hk0 : (0 : ℝ) < k' := by exact_mod_cast hk
  have hB0 : ∀ l, l < L → 0 ≤ Bs l := fun l hl => le_trans hk0.le (hBs l hl)
  have hc : ∀ u, u < L →
      fT' k' (Bs u) / 2 ≤ fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1))) := by
    intro u hu
    have hn := fT'_nonneg k' (Bs u) (hB0 u hu)
    by_cases h0 : u = 0
    · rw [if_pos h0]; linarith
    · rw [if_neg h0]
      have e : u - 1 + 1 = u := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero h0)
      have h := h4 (u - 1) (by rw [e]; exact hu)
      rw [e] at h
      have := fT'_half k' (Bs u) (Bs (u - 1)) (hBs u hu) h
      linarith
  have hc0 : ∀ u, u < L → 0 ≤ fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1))) := by
    intro u hu
    have hn := fT'_nonneg k' (Bs u) (hB0 u hu)
    linarith [hc u hu]
  have hmain : (∑ l ∈ range L, fT k' (al l)) - (∑ l ∈ range L, fT k' (Bs l)) ≤
      ∑ u ∈ range L, (fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1)))) *
        ((∑ l ∈ Ico u L, al l) - (∑ l ∈ Ico u L, Bs l)) := by
    have h := abel_tails (fun l => fT' k' (Bs l)) (fun l => al l - Bs l) L
    simp only [Finset.sum_sub_distrib] at h
    rw [← h, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro l hl
    exact fT_concave k' (al l) (Bs l) (hal l) (hB0 l (Finset.mem_range.mp hl))
  have hterm : ∀ u ∈ range L, (fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1)))) *
        ((∑ l ∈ Ico u L, al l) - (∑ l ∈ Ico u L, Bs l)) ≤ 0 := by
    intro u hu
    have hu' := Finset.mem_range.mp hu
    exact mul_nonpos_of_nonneg_of_nonpos (hc0 u hu') (hDe u hu')
  refine ⟨hc, hmain, Finset.sum_nonpos hterm, ?_⟩
  intro u₀ X hu₀ hX hdef
  constructor
  · refine le_trans hmain ?_
    have h1 := Finset.single_le_sum
      (f := fun u => -((fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1)))) *
        ((∑ l ∈ Ico u L, al l) - (∑ l ∈ Ico u L, Bs l))))
      (fun u hu => neg_nonneg.mpr (hterm u hu)) (Finset.mem_range.mpr hu₀)
    rw [Finset.sum_neg_distrib] at h1
    have h2 := mul_le_mul_of_nonneg_left hdef (hc0 u₀ hu₀)
    have h3 := mul_le_mul_of_nonneg_right (hc u₀ hu₀) hX
    linarith
  · have h := fT'_lower2 k' (Bs u₀) (hBs u₀ hu₀) hk
    have hBp : 0 < Bs u₀ := lt_of_lt_of_le hk0 (hBs u₀ hu₀)
    have e : X * k' / (4 * Bs u₀) = X * ((k' : ℝ) / (2 * Bs u₀)) / 2 := by
      field_simp
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h hX
    linarith
end Formalism.InvariantFactorPaths.BranchingDimensions

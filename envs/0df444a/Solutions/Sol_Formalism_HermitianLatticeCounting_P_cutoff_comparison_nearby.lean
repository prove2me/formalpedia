-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.cutoff_comparison_nearby
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:05.463291+00:00
-- url     : https://prove2.me/submissions/395b0c22-0706-4800-88b8-73dd4a599907

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_E3cut_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (K ro abelian₂ : ℝ) (hK : 0 ≤ K) (hro : 0 < ro) (hLam : 0 < abelian₂) (D x : ℂ)
    (hx : ‖x - D‖ < ro / 2) :
    TruncationCutoff K abelian₂ ‖D‖ ≤ TruncationCutoff K (3 / 2 * max ro abelian₂) ‖x‖ := by
  have hL1 : ro ≤ max ro abelian₂ := le_max_left _ _
  have hL2 : abelian₂ ≤ max ro abelian₂ := le_max_right _ _
  set L := max ro abelian₂ with hL
  have hL0 : 0 < L := lt_of_lt_of_le hro hL1
  by_cases hx0 : ‖x‖ = 0
  · have : TruncationCutoff K (3 / 2 * L) ‖x‖ = 1 := by simp [TruncationCutoff, hx0]
    rw [this]; exact E3cut_le_one _ _ _
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
    have : TruncationCutoff K (3 / 2 * L) ‖x‖ = min 1 ((3 / 2 * L / ‖x‖) ^ K) := by simp [TruncationCutoff, hx0]
    rw [this]
    apply le_min (E3cut_le_one _ _ _)
    by_cases hc : ‖x‖ ≤ 3 / 2 * L
    · have h1 : 1 ≤ 3 / 2 * L / ‖x‖ := by rwa [le_div_iff₀ hxpos, one_mul]
      exact le_trans (E3cut_le_one _ _ _) (Real.one_le_rpow h1 hK)
    · rw [not_le] at hc
      have h1 : ‖x‖ ≤ ‖D‖ + ‖x - D‖ := norm_le_norm_add_norm_sub' x D
      have hD : ‖x‖ ≤ 3 / 2 * ‖D‖ := by linarith
      have hDpos : 0 < ‖D‖ := by linarith
      have : TruncationCutoff K abelian₂ ‖D‖ = min 1 ((abelian₂ / ‖D‖) ^ K) := by simp [TruncationCutoff, hDpos.ne']
      rw [this]
      apply le_trans (min_le_right _ _)
      apply Real.rpow_le_rpow (by positivity) _ hK
      rw [div_le_div_iff₀ hDpos hxpos]
      calc abelian₂ * ‖x‖ ≤ L * (3 / 2 * ‖D‖) := by gcongr
        _ = 3 / 2 * L * ‖D‖ := by ring
end Formalism.HermitianLatticeCounting.P

-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk2.summ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:32:55.382857+00:00
-- url     : https://prove2.me/submissions/d3628cbf-a241-4e64-8fd0-08cb90b5c38d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelCellContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk2
namespace Formalism.L2.Th1.F.Hk2
theorem _root_.solution : Summable (fun p : ℤ × ℤ => ((|(p.1 : ℝ)| + |(p.2 : ℝ)|) ^ 3)⁻¹) := by
  have h := EisensteinSeries.summable_one_div_norm_rpow (k := 3) (by norm_num)
  rw [← (finTwoArrowEquiv ℤ).symm.summable_iff] at h
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) h
  simp only [Function.comp, finTwoArrowEquiv_symm_apply]
  have hN : ‖![p.1, p.2]‖ = max |(p.1 : ℝ)| |(p.2 : ℝ)| := by
    rw [EisensteinSeries.norm_eq_max_natAbs]
    simp [Nat.cast_natAbs]
  rw [hN]
  have q1 : 0 ≤ |(p.1 : ℝ)| := abs_nonneg _
  have q2 : 0 ≤ |(p.2 : ℝ)| := abs_nonneg _
  rcases eq_or_lt_of_le (le_max_of_le_left q1 : 0 ≤ max |(p.1 : ℝ)| |(p.2 : ℝ)|) with h0 | h0
  · have z1 : |(p.1 : ℝ)| = 0 := le_antisymm (h0 ▸ le_max_left _ _) q1
    have z2 : |(p.2 : ℝ)| = 0 := le_antisymm (h0 ▸ le_max_right _ _) q2
    rw [z1, z2]
    simp
  · rw [Real.rpow_neg h0.le]
    have : (max |(p.1 : ℝ)| |(p.2 : ℝ)|) ^ (3 : ℝ) = (max |(p.1 : ℝ)| |(p.2 : ℝ)|) ^ 3 := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [this]
    apply inv_anti₀ (by positivity)
    gcongr
    exact max_le (by linarith) (by linarith)
end Formalism.L2.Th1.F.Hk2

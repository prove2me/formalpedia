-- Prove2me | solution 1 for GenFrameSpan.stepBack
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:51:23.633984+00:00
-- url     : https://prove2.me/submissions/29f642c3-2ed3-4fcb-898d-bceb1b181574

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_StepBack

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
open Classical
open GenFrameSpan
open CutKW
namespace GenFrameSpan
theorem _root_.solution : StepBack := by
  intro Lt _ _ l _ N0 N1 nu Th B h I m
  obtain ⟨c, hc, heq⟩ := h I
  rw [heq]
  have hC : (0 : ℝ) ≤ (l : ℝ) ^ (-B) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [Finsupp.sum, MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun J _ => ?_
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, norm_mul]
  have h1 : ‖(Int.castRingHom ℂ_[l]) (MvPolynomial.coeff m (nablaX N0 nu J))‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_intCast_le_one ℂ_[l] (MvPolynomial.coeff m (nablaX N0 nu J))
  calc ‖c J‖ * ‖(Int.castRingHom ℂ_[l]) (MvPolynomial.coeff m (nablaX N0 nu J))‖
      ≤ (l : ℝ) ^ (-B) * 1 := mul_le_mul (hc J) h1 (norm_nonneg _) hC
    _ = _ := mul_one _
end GenFrameSpan

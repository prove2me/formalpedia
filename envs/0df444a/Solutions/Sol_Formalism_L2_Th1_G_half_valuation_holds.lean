-- Prove2me | solution 1 for Formalism.L2.Th1.G.half_valuation_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:28.85598+00:00
-- url     : https://prove2.me/submissions/c11d1863-7ddc-46e9-97b7-31c04f36d6d8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_InverseEndoIntegralHolds

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.G (unitBall)
namespace Formalism.L2.Th1.G
theorem _root_.solution : HalfValuation := by
  intro K _ S c d hc hd hS
  have hdpos : 0 < ‖(d : K)‖ := norm_pos_iff.mpr hd
  have hcn : ‖c‖ ^ 2 = ‖(d : K)‖ := by rw [← norm_pow, hc, norm_neg]
  have hcpos : 0 < ‖c‖ := by
    rcases (norm_nonneg c).lt_or_eq with h | h
    · exact h
    · rw [← h] at hcn
      simp at hcn
      exact absurd hcn.symm (ne_of_gt hdpos)
  have hsq : ‖(d : K)‖ ^ (1 / 2 : ℝ) = ‖c‖ := by
    rw [← hcn, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg c)]
  rw [Real.rpow_neg hdpos.le, hsq]
  rw [norm_mul] at hS
  rw [← one_div, le_div_iff₀ hcpos, mul_comm]
  exact hS
end Formalism.L2.Th1.G

-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk1.hk_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:45:06.703714+00:00
-- url     : https://prove2.me/submissions/a2baeab3-0374-4f0a-8330-e5cc02e8e488

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelIntegralValue
import Theorems.Thm_P2M_Formalism_L2_Th1_F_Hk1_rpow_neg_two__f5e7837d33f8

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
open MeasureTheory Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk1
namespace Formalism.L2.Th1.F.Hk1
theorem _root_.solution (s a : ℝ) (ha : 0 < a) (w : ℂ) :
    hk s ((a : ℂ) * w) = ((a ^ (-(2 + 2 * s)) : ℝ) : ℂ) * hk s w := by
  unfold hk
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le,
    Real.mul_rpow ha.le (norm_nonneg _),
    show -(2 + 2 * s) = (-2 : ℝ) + -(2 * s) by ring, Real.rpow_add ha, rpow_neg_two' ha]
  push_cast
  ring
end Formalism.L2.Th1.F.Hk1

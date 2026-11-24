-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk1.norm_hk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:45:08.411799+00:00
-- url     : https://prove2.me/submissions/a8a62c4f-2ab2-4d2c-9c27-915cc9c1c799

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
theorem _root_.solution (s : ℝ) (w : ℂ) (hw : w ≠ 0) : ‖hk s w‖ = ‖w‖ ^ (-(2 + 2 * s)) := by
  have h0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
  unfold hk
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg h0.le _)]
  rw [show -(2 + 2 * s) = (-2 : ℝ) + -(2 * s) by ring, Real.rpow_add h0, rpow_neg_two' h0]
end Formalism.L2.Th1.F.Hk1

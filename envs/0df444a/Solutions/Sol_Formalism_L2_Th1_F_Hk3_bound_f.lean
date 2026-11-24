-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk3.bound_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:48:23.631798+00:00
-- url     : https://prove2.me/submissions/884fdf71-45c9-438c-a61d-d06afa9b621b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelLineZero
import Theorems.Thm_Formalism_L2_Th1_F_Hk3_one_add_sq_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk3
namespace Formalism.L2.Th1.F.Hk3
theorem _root_.solution {a : ℝ} (t : ℝ) : ‖t * (1 + t ^ 2) ^ (-a)‖ ≤ (1 + t ^ 2) ^ (-(a - 1 / 2)) := by
  have hp := one_add_sq_pos t
  have h1 : |t| ≤ (1 + t ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.abs_le_sqrt (by linarith)
  have h2 : (1 + t ^ 2) ^ (-(a - 1 / 2)) = (1 + t ^ 2) ^ ((1 : ℝ) / 2) * (1 + t ^ 2) ^ (-a) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp.le _), h2]
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hp.le _)
end Formalism.L2.Th1.F.Hk3

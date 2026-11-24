-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk3.hasDeriv_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:48:24.411314+00:00
-- url     : https://prove2.me/submissions/8eeab9ee-a50a-45cf-a8d5-f3d5708c64cf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelLineZero
import Theorems.Thm_Formalism_L2_Th1_F_Hk3_one_add_sq_pos
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul


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
theorem _root_.solution (a t : ℝ) :
    HasDerivAt (fun t : ℝ => t * (1 + t ^ 2) ^ (-a))
      ((1 - 2 * a) * (1 + t ^ 2) ^ (-a) + 2 * a * (1 + t ^ 2) ^ (-(a + 1))) t := by
  have hp := one_add_sq_pos t
  have h0 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add 1
  have h1 := h0.rpow_const (p := -a) (Or.inl hp.ne')
  have h2 := (hasDerivAt_id t).mul h1
  refine h2.congr_deriv ?_
  have h3 : (1 + t ^ 2) ^ (-a) = (1 + t ^ 2) * (1 + t ^ 2) ^ (-(a + 1)) := by
    nth_rewrite 2 [← Real.rpow_one (1 + t ^ 2)]
    rw [← Real.rpow_add hp]
    congr 1
    ring
  have h4 : -a - 1 = -(a + 1) := by ring
  simp only [id, h4]
  rw [h3]
  ring
end Formalism.L2.Th1.F.Hk3

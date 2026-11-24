-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk1.summable_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:34:01.064167+00:00
-- url     : https://prove2.me/submissions/1600b216-5a1f-47b7-83e9-df486c45bb0c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelIntegralValue

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
theorem _root_.solution (z : UpperHalfPlane) (s : ℝ) (hs : 0 < s) :
    Summable (fun p : ℤ × ℤ => ‖(p.1 : ℂ) + (p.2 : ℂ) * (z : ℂ)‖ ^ (-(2 + 2 * s))) := by
  have h1 := (EisensteinSeries.summable_one_div_norm_rpow (k := 2 + 2 * s) (by linarith)).mul_left
    ((EisensteinSeries.r z) ^ (-(2 + 2 * s)))
  have h2 : Summable (fun x : Fin 2 → ℤ => ‖(x 0 : ℂ) * (z : ℂ) + x 1‖ ^ (-(2 + 2 * s))) :=
    Summable.of_nonneg_of_le (fun x => Real.rpow_nonneg (norm_nonneg _) _)
      (fun x => EisensteinSeries.summand_bound z (by linarith) x) h1
  have h3 := (((Equiv.prodComm ℤ ℤ).trans (finTwoArrowEquiv ℤ).symm).summable_iff).mpr h2
  refine h3.congr (fun p => ?_)
  simp [add_comm]
end Formalism.L2.Th1.F.Hk1

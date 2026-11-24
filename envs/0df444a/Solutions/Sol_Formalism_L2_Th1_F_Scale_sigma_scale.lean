-- Prove2me | solution 1 for Formalism.L2.Th1.F.Scale.sigma_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:51:54.011972+00:00
-- url     : https://prove2.me/submissions/d41284b0-26e3-4a43-ba4b-bdaa85336e26

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Theorems.Thm_Formalism_L2_Th1_F_Scale_sigS_scale
import Theorems.Thm_Formalism_L2_Th1_B_Map_cc_sigS
import Theorems.Thm_Formalism_L2_Th1_B_Sq_rescale_fExp


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
open Formalism.L2.Th1.CM (cW wpNum wpDen uSer)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Scale
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.F.Scale
theorem _root_.solution (lam : K) (P : PowerSeries K) :
    C lam * Formalism.L2.Th1.B.sigma (C (lam ^ 2) * rescale lam P)
      = rescale lam (Formalism.L2.Th1.B.sigma P) := by
  unfold Formalism.L2.Th1.B.sigma
  rw [map_mul, rescale_X, Formalism.L2.Th1.B.Sq.rescale_fExp lam (Formalism.L2.Th1.B.Map.cc_sigS P),
    sigS_scale, mul_assoc]
end Formalism.L2.Th1.F.Scale

-- Prove2me | solution 1 for Formalism.L2.Th1.F.Scale.sigS_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:36:11.808643+00:00
-- url     : https://prove2.me/submissions/1ccfb094-ff0d-4a3a-abc0-2fbf68d16ce3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Theorems.Thm_Formalism_L2_Th1_F_Scale_prim_scale
import Theorems.Thm_Formalism_L2_Th1_F_Scale_prim_C_mul

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
    Formalism.L2.Th1.B.sigS (C (lam ^ 2) * rescale lam P) = rescale lam (Formalism.L2.Th1.B.sigS P) := by
  unfold Formalism.L2.Th1.B.sigS
  rw [map_neg, ← prim_scale, ← prim_scale, ← prim_C_mul, ← mul_assoc, ← map_mul, sq]
end Formalism.L2.Th1.F.Scale

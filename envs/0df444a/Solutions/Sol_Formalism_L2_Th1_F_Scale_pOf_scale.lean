-- Prove2me | solution 1 for Formalism.L2.Th1.F.Scale.pOf_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:00:08.608554+00:00
-- url     : https://prove2.me/submissions/f4836523-95e0-4216-b919-0f64b3ce2d90

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Theorems.Thm_Formalism_L2_Th1_F_Scale_wpNum_scale

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
namespace Formalism.L2.Th1.F.Scale
theorem _root_.solution {K : Type} [Field K] (g2 g3 lam : K) :
    pOf (lam ^ 4 * g2) (lam ^ 6 * g3) = C (lam ^ 2) * rescale lam (pOf g2 g3) := by
  ext n
  rw [coeff_C_mul, coeff_rescale]
  unfold pOf
  rw [coeff_mk, coeff_mk, wpNum_scale, coeff_rescale]
  ring
end Formalism.L2.Th1.F.Scale

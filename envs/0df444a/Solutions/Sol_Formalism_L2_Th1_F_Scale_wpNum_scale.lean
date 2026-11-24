-- Prove2me | solution 1 for Formalism.L2.Th1.F.Scale.wpNum_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:47:19.044819+00:00
-- url     : https://prove2.me/submissions/d2075335-15d7-4422-93d7-507605aef23a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Theorems.Thm_Formalism_L2_Th1_F_Scale_cW_scale

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
    wpNum (lam ^ 4 * g2) (lam ^ 6 * g3) = rescale lam (wpNum g2 g3) := by
  ext n
  rw [coeff_rescale]
  unfold wpNum
  rw [coeff_mk, coeff_mk]
  split_ifs with h0 he
  · subst h0; simp
  · rw [cW_scale, Nat.two_mul_div_two_of_even he]
  · rw [mul_zero]
end Formalism.L2.Th1.F.Scale

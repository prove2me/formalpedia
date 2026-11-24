-- Prove2me | solution 1 for Formalism.L2.Th1.F.Scale.wpDen_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:51:56.04181+00:00
-- url     : https://prove2.me/submissions/c4358e50-d78f-4e6a-8979-7bcabb4248ff

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Theorems.Thm_Formalism_L2_Th1_F_Scale_cW_map

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
variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')
namespace Formalism.L2.Th1.F.Scale
theorem _root_.solution (g2 g3 : K) : map φ (wpDen g2 g3) = wpDen (φ g2) (φ g3) := by
  ext n
  rw [coeff_map]
  unfold wpDen
  rw [coeff_mk, coeff_mk]
  split_ifs
  · exact map_one φ
  · rw [map_mul, map_neg, map_sub, map_natCast, map_one, cW_map]
  · exact map_zero φ
end Formalism.L2.Th1.F.Scale

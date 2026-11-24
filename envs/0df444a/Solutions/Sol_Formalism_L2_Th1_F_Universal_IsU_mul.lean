-- Prove2me | solution 1 for Formalism.L2.Th1.F.Universal.IsU.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:35:07.170482+00:00
-- url     : https://prove2.me/submissions/48bd30e3-4b4c-40d1-85fb-c645a8956878

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Universal
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


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
open Formalism.L2.Th1.CM (cW)
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Universal
namespace Formalism.L2.Th1.F.Universal
namespace IsU
theorem _root_.solution {a b : ∀ (K : Type) [Field K] [CharZero K], K → K → K} (ha : IsU a) (hb : IsU b) :
    IsU (fun K [Field K] [CharZero K] g2 g3 => a K g2 g3 * b K g2 g3) := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  exact ⟨p * q, fun K _ _ g2 g3 => by
    show a K g2 g3 * b K g2 g3 = _
    rw [map_mul, hp, hq]⟩
end IsU
end Formalism.L2.Th1.F.Universal

-- Prove2me | solution 1 for Formalism.L2.Th1.F.Universal.IsU.congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:32:17.065716+00:00
-- url     : https://prove2.me/submissions/7388c8dc-216c-4a37-8fa0-95312d70cfa6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Universal

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
theorem _root_.solution {a b : ∀ (K : Type) [Field K] [CharZero K], K → K → K} (h : IsU a)
    (hab : ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K), b K g2 g3 = a K g2 g3) : IsU b := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun K _ _ g2 g3 => by rw [hab, hp]⟩
end IsU
end Formalism.L2.Th1.F.Universal

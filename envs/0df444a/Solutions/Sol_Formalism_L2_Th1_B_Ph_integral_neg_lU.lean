-- Prove2me | solution 1 for Formalism.L2.Th1.B.Ph.integral_neg_lU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:21:21.192796+00:00
-- url     : https://prove2.me/submissions/72f4c5b7-d3c4-43ac-a2a7-04605b387e3d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Ph
open PowerSeries
open Formalism.DworkPowerSeriesWeights (Integral)
namespace Formalism.L2.Th1.B.Ph
theorem _root_.solution {K : Type} [NormedField K] {i : PowerSeries K}
    (hi : Integral (ι := Unit) i) : Integral (ι := Unit) (-lU i) := by
  intro n
  rw [map_neg, norm_neg]
  exact hi (Finsupp.single () (n () + 1))
end Formalism.L2.Th1.B.Ph

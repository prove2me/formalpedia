-- Prove2me | solution 1 for Formalism.L2.Th1.C.derivative_pExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:39.849435+00:00
-- url     : https://prove2.me/submissions/2e5d4638-f667-4e2c-a6d4-a11af198c403

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ChordSecondLogDeriv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_HasSecondLogDerivPowerSeriesExp

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
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.C
theorem _root_.solution (f : PowerSeries K) (hf : constantCoeff f = 0) :
    derivative K (pExp f) = pExp f * derivative K f := by
  have hs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf
  show derivative K (PowerSeries.subst f (PowerSeries.exp K)) =
    PowerSeries.subst f (PowerSeries.exp K) * derivative K f
  rw [PowerSeries.derivative_subst hs, PowerSeries.derivative_exp]
end Formalism.L2.Th1.C

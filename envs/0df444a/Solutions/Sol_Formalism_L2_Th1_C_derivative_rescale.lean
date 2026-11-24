-- Prove2me | solution 1 for Formalism.L2.Th1.C.derivative_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:22:47.377517+00:00
-- url     : https://prove2.me/submissions/6264ab74-a213-45fe-9f38-b1cd88509ed5

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
theorem _root_.solution (a : K) (f : PowerSeries K) :
    derivative K (rescale a f) = a • rescale a (derivative K f) := by
  ext n
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
  ring
end Formalism.L2.Th1.C

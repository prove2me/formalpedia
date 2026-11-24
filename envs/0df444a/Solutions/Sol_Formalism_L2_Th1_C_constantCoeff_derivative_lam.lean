-- Prove2me | solution 1 for Formalism.L2.Th1.C.constantCoeff_derivative_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:23:11.861721+00:00
-- url     : https://prove2.me/submissions/a768e5f6-ad96-4915-b8aa-02f362918ebf

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
theorem _root_.solution (e : PowerSeries K) (s2 : K) :
    constantCoeff (derivative K (lam e s2)) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
  simp [lam, dblInt, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
end Formalism.L2.Th1.C

-- Prove2me | solution 1 for Formalism.L2.Th1.C.constantCoeff_pExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:23:12.633827+00:00
-- url     : https://prove2.me/submissions/b3f9cb2f-b461-4444-a3d6-f74fc60863a4

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
theorem _root_.solution (hE : MvExpLaws) (f : PowerSeries K) (hf : constantCoeff f = 0) :
    constantCoeff (pExp f) = 1 := (hE K Unit).2.1 f hf
end Formalism.L2.Th1.C

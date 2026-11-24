-- Prove2me | solution 1 for Formalism.L2.Th1.C.pExp_mul_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:23:07.083427+00:00
-- url     : https://prove2.me/submissions/48a31f5e-226e-45cb-84c7-d050272c08c5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ChordSecondLogDeriv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_HasSecondLogDerivPowerSeriesExp
import Theorems.Thm_Formalism_L2_Th1_C_pExp_zero
import Theorems.Thm_Formalism_L2_Th1_C_pExp_add

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
    pExp f * pExp (-f) = 1 := by
  rw [← pExp_add hE f (-f) hf (by rw [map_neg, hf, neg_zero]), add_neg_cancel, pExp_zero hE]
end Formalism.L2.Th1.C

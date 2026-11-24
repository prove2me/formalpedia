-- Prove2me | solution 1 for Formalism.L2.Th1.C.isUnit_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:23:14.916422+00:00
-- url     : https://prove2.me/submissions/24e382ec-ad5d-4c71-81e3-0d22c960e75e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_mul_neg

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
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K] {σ : Type}
namespace Formalism.L2.Th1.C
theorem _root_.solution {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    IsUnit (mvExp f) := isUnit_iff_exists_inv.2 ⟨_, mvExp_mul_neg hf⟩
end Formalism.L2.Th1.C

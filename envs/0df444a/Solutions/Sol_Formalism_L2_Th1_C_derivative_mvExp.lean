-- Prove2me | solution 1 for Formalism.L2.Th1.C.derivative_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:42.462736+00:00
-- url     : https://prove2.me/submissions/091e6ed4-21bc-40ad-a797-403d6e835a70

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Theorems.Thm_Formalism_L2_Th1_C_hasSubst_of_cc

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
theorem _root_.solution {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.derivative K (mvExp f : PowerSeries K) =
      PowerSeries.derivative K f * (mvExp f : PowerSeries K) := by
  unfold mvExp
  rw [PowerSeries.derivative_subst (hasSubst_of_cc hf), PowerSeries.derivative_exp, mul_comm]
end Formalism.L2.Th1.C

-- Prove2me | solution 1 for Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.pderiv_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:49:28.792036+00:00
-- url     : https://prove2.me/submissions/0a678262-d58f-4937-8849-72335c07b88b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_pderiv_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
variable {K : Type} [Field K] [CharZero K] {σ : Type}
namespace Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
theorem _root_.solution {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) (i : σ) :
    MvPowerSeries.pderiv K i (mvExp f) = mvExp f * MvPowerSeries.pderiv K i f := by
  unfold mvExp
  rw [pderiv_subst _ hf, derivative_exp]
end Formalism.L2.Th1.C.IntegralMvPolynomialLemmas

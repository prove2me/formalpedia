-- Prove2me | solution 1 for Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.pderiv_subst_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:22:08.294559+00:00
-- url     : https://prove2.me/submissions/2446b2bb-d59b-495c-9647-d023983ae360

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal

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
variable {A : Type*} [CommRing A] {σ : Type*}
namespace Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
theorem _root_.solution (p : Polynomial A) {a : MvPowerSeries σ A}
    (ha : MvPowerSeries.constantCoeff a = 0) (i : σ) :
    MvPowerSeries.pderiv A i ((p : PowerSeries A).subst a) =
      (derivative A (p : PowerSeries A)).subst a * MvPowerSeries.pderiv A i a := by
  have hs : HasSubst a := HasSubst.of_constantCoeff_zero ha
  rw [subst_coe hs, derivative_coe, subst_coe hs, Derivation.comp_aeval_eq, smul_eq_mul]
end Formalism.L2.Th1.C.IntegralMvPolynomialLemmas

-- Prove2me | solution 1 for Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.pderiv_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:33:49.393868+00:00
-- url     : https://prove2.me/submissions/94423d21-fec6-4208-86e8-ba363c3728d0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_coeff_subst_congr
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_pderiv_subst_coe
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_degree_le_of_mem_antidiagonal

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
theorem _root_.solution (g : PowerSeries A) {a : MvPowerSeries σ A}
    (ha : MvPowerSeries.constantCoeff a = 0) (i : σ) :
    MvPowerSeries.pderiv A i (g.subst a) =
      (derivative A g).subst a * MvPowerSeries.pderiv A i a := by
  classical
  ext d
  have hdeg : (d + Finsupp.single i 1).degree = d.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have h1 : MvPowerSeries.coeff (d + Finsupp.single i 1) (g.subst a) =
      MvPowerSeries.coeff (d + Finsupp.single i 1)
        (((trunc (d.degree + 2) g : Polynomial A) : PowerSeries A).subst a) := by
    apply coeff_subst_congr ha
    intro k hk
    rw [coeff_coe_trunc_of_lt (by omega)]
  rw [MvPowerSeries.coeff_pderiv, h1, ← MvPowerSeries.coeff_pderiv, pderiv_subst_coe _ ha,
    MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  congr 1
  apply coeff_subst_congr ha
  intro k hk
  have := degree_le_of_mem_antidiagonal hx
  rw [coeff_derivative, coeff_derivative, coeff_coe_trunc_of_lt (by omega)]
end Formalism.L2.Th1.C.IntegralMvPolynomialLemmas

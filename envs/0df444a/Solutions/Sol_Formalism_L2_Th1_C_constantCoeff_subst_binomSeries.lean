-- Prove2me | solution 1 for Formalism.L2.Th1.C.constantCoeff_subst_binomSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:23:13.344796+00:00
-- url     : https://prove2.me/submissions/8bcd247b-c955-46bd-af29-2242835854f3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffSubstBinomSeries
import Theorems.Thm_Formalism_L2_Th1_C_binom_zero
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_coeff_subst_congr


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
theorem _root_.solution (z : K) {g : MvPowerSeries σ K}
    (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst g (binomSeries z)) = 1 := by
  have h := IntegralMvPolynomialLemmas.coeff_subst_congr (g := binomSeries z) (h := PowerSeries.C (1 : K)) hg 0
    (fun k hk => by
      have : k = 0 := by simpa using hk
      subst this
      simp [binomSeries, binom_zero])
  rw [PowerSeries.subst_C] at h
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  simp
end Formalism.L2.Th1.C

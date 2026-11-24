-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.coeff_one_linv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:22:04.98679+00:00
-- url     : https://prove2.me/submissions/a1b9ad9d-2ea7-4ab5-b051-49ad93eb3329

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Theorems.Thm_Formalism_L2_Th1_C_Pts_hasSubst
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Pts
open IntegralMvPolynomialLemmas
variable {K : Type} [Field K] {σ : Type} {l linv : PowerSeries K}
namespace Formalism.L2.Th1.C.Pts
theorem _root_.solution (h : IsLogPair l linv) : PowerSeries.coeff 1 linv = 1 := by
  have hc := coeff_subst_congr (g := linv)
    (h := PowerSeries.C (PowerSeries.coeff 1 linv) * PowerSeries.X) (a := l) h.1
    (Finsupp.single () 1) (fun k hk => by
      rw [Finsupp.degree_single] at hk
      interval_cases k
      · simp [h.2.2.1]
      · simp)
  rw [h.2.2.2.1, PowerSeries.subst_mul (hasSubst h.1), PowerSeries.subst_C,
    PowerSeries.subst_X (hasSubst h.1)] at hc
  have h1 : PowerSeries.coeff 1 (PowerSeries.X : PowerSeries K) =
      PowerSeries.coeff 1 (PowerSeries.C (PowerSeries.coeff 1 linv) * l) := hc
  rw [PowerSeries.coeff_one_X, PowerSeries.coeff_C_mul, h.2.1, mul_one] at h1
  exact h1.symm
end Formalism.L2.Th1.C.Pts

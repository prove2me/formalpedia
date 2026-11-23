-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.coeff_substMv_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:31.305806+00:00
-- url     : https://prove2.me/submissions/debd2d30-a967-439f-86b0-225b27b16ec6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points

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
variable {K : Type} [Field K] {σ : Type} {R : Subring K} {l linv : PowerSeries K}
namespace Formalism.L2.Th1.C.Pts
theorem _root_.solution {τ : Type} (F : MvPowerSeries (Fin 2) K) {a : Fin 2 → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.subst a F) =
      finsum fun d : Fin 2 →₀ ℕ =>
        MvPowerSeries.coeff d F * MvPowerSeries.coeff e (a 0 ^ d 0 * a 1 ^ d 1) := by
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  refine finsum_congr fun d => ?_
  rw [smul_eq_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
end Formalism.L2.Th1.C.Pts

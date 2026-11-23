-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.coeff_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:29.071489+00:00
-- url     : https://prove2.me/submissions/5729fda2-f428-4533-8701-d31c578fcffe

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
theorem _root_.solution {i : PowerSeries K} {n : ℕ} (hi : ∀ m < n, PowerSeries.coeff m i ∈ R)
    (k : ℕ) : ∀ m < n, PowerSeries.coeff m (i ^ k) ∈ R := by
  induction k with
  | zero =>
    intro m _
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  | succ k ih =>
    intro m hm
    rw [pow_succ, PowerSeries.coeff_mul]
    refine Subring.sum_mem _ fun p hp => ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    exact R.mul_mem (ih _ (by omega)) (hi _ (by omega))
end Formalism.L2.Th1.C.Pts

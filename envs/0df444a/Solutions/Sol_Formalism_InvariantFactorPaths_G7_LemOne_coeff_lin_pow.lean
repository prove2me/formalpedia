-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.coeff_lin_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:56.780417+00:00
-- url     : https://prove2.me/submissions/f7f90410-7fe4-4b2a-9e08-08b9d3c791b1

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LemOne
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.LemOne
theorem _root_.solution (n i : ℕ) (hi : i ≤ n) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (n - i))
      ((MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ n) = (n.choose i : K) := by
  classical
  rw [add_pow, map_sum, Finset.sum_eq_single i]
  · rw [← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := K)), MvPowerSeries.coeff_mul_C,
      MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial,
      MvPowerSeries.coeff_monomial_same]
    simp
  · intro m _ hm
    rw [← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := K)), MvPowerSeries.coeff_mul_C,
      MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial,
      MvPowerSeries.coeff_monomial, if_neg, zero_mul]
    intro h
    apply hm
    have := congrArg (fun e => e 0) h
    simpa using this.symm
  · intro h
    exact absurd (mem_range.mpr (by omega)) h
end Formalism.InvariantFactorPaths.G7.LemOne

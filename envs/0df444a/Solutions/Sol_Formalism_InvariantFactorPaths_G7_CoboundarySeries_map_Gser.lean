-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoboundarySeries.map_Gser
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:33.303555+00:00
-- url     : https://prove2.me/submissions/f68317c6-80e4-4539-b22e-38c4d1cf52b7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree

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
open Formalism.InvariantFactorPaths.G7.CoboundarySeries
open MvPowerSeries
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.CoboundarySeries
theorem _root_.solution (σ : K →+* K) (p : ℕ) (c c' : K) :
    map σ (Gser p c c') = Gser p (σ c) (σ c') := by
  have hA : MvPowerSeries.map σ (Aser K p) = Aser K p := by
    ext n
    rw [MvPowerSeries.coeff_map]
    change σ (Aser K p n) = Aser K p n
    simp only [Aser, map_sum, apply_ite σ, map_inv₀, map_pow, map_natCast, map_zero]
  have hA' : MvPowerSeries.map σ (Aser' K p) = Aser' K p := by
    ext n
    rw [MvPowerSeries.coeff_map]
    change σ (Aser' K p n) = Aser' K p n
    simp only [Aser', map_sum, apply_ite σ, map_inv₀, map_pow, map_natCast, map_zero]
  unfold Gser
  rw [map_sub, map_mul, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_C, hA, hA']
end Formalism.InvariantFactorPaths.G7.CoboundarySeries

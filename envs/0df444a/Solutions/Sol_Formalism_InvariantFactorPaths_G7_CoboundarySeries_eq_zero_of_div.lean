-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoboundarySeries.eq_zero_of_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:24.618943+00:00
-- url     : https://prove2.me/submissions/bbb0ebf9-a7ff-4bfc-ba32-aa816a8942a1

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
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.CoboundarySeries
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {x : K}
    (h : ∀ i : ℕ, ‖x * ((p : K) ^ (i + 1))⁻¹‖ ≤ 1) : x = 0 := by
  by_contra hx
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hq : ((p : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ hp1
  have hq0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one hx0 hq
  have h1 := h i
  rw [norm_mul, norm_inv, norm_pow, hnp] at h1
  have hpos : 0 < ((p : ℝ)⁻¹) ^ (i + 1) := by positivity
  rw [mul_inv_le_iff₀ hpos, one_mul] at h1
  have h2 : ((p : ℝ)⁻¹) ^ (i + 1) ≤ ((p : ℝ)⁻¹) ^ i := pow_le_pow_of_le_one hq0 hq.le (by omega)
  linarith
end Formalism.InvariantFactorPaths.G7.CoboundarySeries

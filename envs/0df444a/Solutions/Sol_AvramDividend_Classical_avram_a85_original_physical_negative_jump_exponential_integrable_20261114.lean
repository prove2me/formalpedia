-- Prove2me | solution 1 for AvramDividend.Classical.avram_a85_original_physical_negative_jump_exponential_integrable_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:12:14.709003+00:00
-- url     : https://prove2.me/submissions/036a265b-0e42-4d45-93f0-1cfbcba92fd9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a66_original_finiteactivity_actual_cumulative_negative_jump_sum_nonpos_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a35_finite_support_causal_marked_tsum_eq_finite_sum_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a67_nonpositive_jump_exponential_bounded_integrable_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ T then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0) :
    Integrable (fun ω => Real.exp (θ * J ω)) P ∧
    (∀ᵐ ω ∂P,
      0 < Real.exp (θ * J ω) ∧
      Real.exp (θ * J ω) ≤ 1) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hFiniteS :=
    avram_a66_original_finiteactivity_actual_cumulative_negative_jump_sum_nonpos_20261114
      X hFinite
  have hNonpos : ∀ᵐ ω ∂P, J ω ≤ 0 := by
    filter_upwards [hFiniteS, hJEq] with ω hF hJe
    obtain ⟨S, hSupport, hPartial⟩ := hF T
    have hSum :=
      avram_a35_finite_support_causal_marked_tsum_eq_finite_sum_20261114
        (fun u : ℝ≥0 => X.X u ω -
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u)
        T S hSupport T le_rfl
    rw [hJe, hSum]
    exact hPartial T le_rfl
  exact avram_a67_nonpositive_jump_exponential_bounded_integrable_20261114
    J θ hJMeas hθ hNonpos

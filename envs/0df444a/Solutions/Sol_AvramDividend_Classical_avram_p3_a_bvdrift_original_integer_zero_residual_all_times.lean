-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_integer_zero_residual_all_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:57:26.915784+00:00
-- url     : https://prove2.me/submissions/a7d5abb0-9805-40d3-8ca2-83625f3afefe

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Countably many zero canonical residuals at integer times force zero at
all times along the same original monotone BV Levy source path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hzeros : ∀ᵐ ω ∂P, ∀ n : ℕ,
      (((n : ℝ≥0) : ℝ) * X.drift - X.X (n : ℝ≥0) ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ (n : ℝ≥0) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal = 0 := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_canonical_remainder_monotone X hBV,
      hzeros] with ω hmon hzero
  let R : ℝ≥0 → ℝ := fun t =>
    ((t : ℝ) * X.drift - X.X t ω) -
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        ENNReal.ofReal
          (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal
  have hm : Monotone R := hmon
  have hz : ∀ n : ℕ, R (n : ℝ≥0) = 0 := hzero
  intro t
  obtain ⟨n, hn⟩ := exists_nat_ge t
  have hlo : 0 ≤ R t := by
    have h := hm (show (0 : ℝ≥0) ≤ t from zero_le)
    have hzero0 : R (0 : ℝ≥0) = 0 := by simpa using (hz 0)
    rw [hzero0] at h
    exact h
  have hhi : R t ≤ 0 := by
    have h := hm hn
    rw [hz n] at h
    exact h
  exact le_antisymm hhi hlo

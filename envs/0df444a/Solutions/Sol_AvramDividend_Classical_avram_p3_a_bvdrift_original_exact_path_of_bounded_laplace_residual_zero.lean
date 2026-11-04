-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_exact_path_of_bounded_laplace_residual_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:55:10.360667+00:00
-- url     : https://prove2.me/submissions/77755108-cfcb-4fa0-99ed-549aace2b39f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_laplace_integer_zero_forces_original_monotone_residual_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Conditional original-source BV decomposition from bounded exponential
integer-clock residual deficits; characteristic input remains explicit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    let R : ℝ≥0 → Ω → ℝ := fun t ω =>
      (((t : ℝ) * X.drift - X.X t ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))
    (∀ n : ℕ, Integrable
      (fun ω => 1 - Real.exp (-(R (n : ℝ≥0) ω))) P) →
    (∀ n : ℕ, (∫ ω, 1 - Real.exp (-(R (n : ℝ≥0) ω)) ∂P) = 0) →
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.drift -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by
  dsimp only
  intro hInt hMean
  let R : ℝ≥0 → Ω → ℝ := fun t ω =>
    (((t : ℝ) * X.drift - X.X t ω) -
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))
  have hRzero : ∀ ω : Ω, R 0 ω = 0 := by
    intro ω
    have hzero : ∀ u : ℝ≥0, ¬(0 < u ∧ u ≤ (0 : ℝ≥0)) := by
      intro u ⟨hpos, hle⟩
      exact (not_lt_of_ge hle) hpos
    have hsum :
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ (0 : ℝ≥0) then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
          else 0) = 0 := by
      have hterm :
          (fun u : ℝ≥0 => if 0 < u ∧ u ≤ (0 : ℝ≥0) then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
            else 0) = (fun _ => (0 : ℝ)) := by
        funext u
        exact if_neg (hzero u)
      rw [hterm]
      exact tsum_zero
    dsimp only [R]
    rw [hsum]
    simp [X.X_zero ω]
  have hRmono : ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => R t ω) := by
    simpa only [R] using
      (avram_p3_a_bvdrift_original_raw_removed_residual_monotone X hBV)
  have hFull : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, R t ω = 0 :=
    avram_p3_a_bvdrift_laplace_integer_zero_forces_original_monotone_residual_zero
      R hRzero hRmono hInt hMean
  filter_upwards [hFull] with ω hω
  intro t
  have h := hω t
  dsimp [R] at h
  linarith only [h]

-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_all_marks_all_weights_countably_many_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:17:42.78519+00:00
-- url     : https://prove2.me/submissions/a1932c13-b2c4-4ef0-909e-0ce75c35b1cc

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_zero_all_weights_countably_many_clocks

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
One original controlled UBV event simultaneously annihilates exact
predictable cap-contact compensator densities for every member of a
countable family of atomless clocks, every mark measure, and every
nonnegative marked weight, including infinite weights at contact.
-/

/-- Uniform original cap-null marked generator boundary across clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : ℕ → Measure ℝ≥0)
    (hsf : ∀ n, SFinite (μ n))
    (hatom : ∀ n, NullSingletonClass (μ n)) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (ν : Measure ℝ)
      (weight : ℝ≥0 → ℝ → Ω → ℝ≥0∞),
      (∫⁻ t : ℝ≥0, ∫⁻ z : ℝ,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight t z ω else 0 ∂ν ∂μ n) = 0 := by
  have hUniform :=
    avram_wave5_05_ubv_original_predictable_cap_zero_all_weights_countably_many_clocks
      X hBV x c D hD hCap μ hsf hatom
  filter_upwards [hUniform] with ω hω
  intro n ν weight
  have hWeighted := hω n (fun t ω => ∫⁻ z : ℝ, weight t z ω ∂ν)
  have hPoint (t : ℝ≥0) :
      (∫⁻ z : ℝ,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight t z ω else 0 ∂ν) =
      (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
       then (∫⁻ z : ℝ, weight t z ω ∂ν) else 0) := by
    by_cases ht : 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
    · simp [ht]
    · simp [ht]
  calc
    (∫⁻ t : ℝ≥0, ∫⁻ z : ℝ,
      if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
      then weight t z ω else 0 ∂ν ∂μ n) =
      ∫⁻ t : ℝ≥0,
        (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
         then (∫⁻ z : ℝ, weight t z ω ∂ν) else 0) ∂μ n := by
        exact lintegral_congr hPoint
    _ = 0 := hWeighted

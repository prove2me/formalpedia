-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_countable_marked_compensators
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T12:00:16.233635+00:00
-- url     : https://prove2.me/submissions/66442db2-12da-4c88-8a6e-6cf654ab7ae7

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_zero_marked_source_compensator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
All levels of a countable jump-mark truncation or localisation scheme
have zero predictable cap-contact intensity on ONE conull event, while
the true original source X and actual controlled dividends D remain fixed.
-/

/-- Simultaneous original cap-null compensator clocks at countably many
    prescribed atomless times and arbitrary real jump-mark measures. -/
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
    (hatom : ∀ n, NullSingletonClass (μ n))
    (ν : ℕ → Measure ℝ)
    (weight : ℕ → ℝ≥0 → ℝ → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      (∫⁻ t : ℝ≥0, ∫⁻ z : ℝ,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight n t z ω else 0 ∂(ν n) ∂(μ n)) = 0 := by
  apply (ae_all_iff).2
  intro n
  letI : SFinite (μ n) := hsf n
  letI : NullSingletonClass (μ n) := hatom n
  exact avram_wave5_05_ubv_original_predictable_cap_zero_marked_source_compensator
    X hBV x c D hD hCap (μ n) (ν n) (weight n)

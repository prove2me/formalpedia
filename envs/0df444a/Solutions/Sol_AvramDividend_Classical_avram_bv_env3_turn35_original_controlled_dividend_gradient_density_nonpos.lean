-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn35_original_controlled_dividend_gradient_density_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:37:54.428201+00:00
-- url     : https://prove2.me/submissions/be3d3509-a09d-4406-9bab-b2fcde113708

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True controlled dividend Stieltjes gradient density is nonpositive on
    any admissible positive cap-interior payment event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (B : Ω → Set ℝ)
    (hB : ∀ ω s, s ∈ B ω →
      0 < riskProcess X x D s.toNNReal ω ∧
        ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C)
    (q : ℝ) :
    ∀ (ω : Ω) (s : ℝ),
      (if s ∈ B ω then
        Real.exp (-(q * s)) *
          (1 - deriv w (riskProcess X x D s.toNNReal ω))
       else 0) ≤ 0 := by
  intro ω s
  by_cases hs : s ∈ B ω
  · have hsPositive := (hB ω s hs).1
    have hsCap := (hB ω s hs).2
    have hsGradient := hw_grad _ hsPositive hsCap
    have hnonpos : Real.exp (-(q * s)) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (Real.exp_pos _).le (sub_nonpos.mpr hsGradient)
    simpa [hs] using hnonpos
  · simp [hs]

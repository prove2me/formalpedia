-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn34_original_HJB_drift_plus_stieltjes_gradient_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:36:34.603209+00:00
-- url     : https://prove2.me/submissions/e7429104-78d0-4ff6-8e2d-17b2e919ee7b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn26_original_localised_HJB_signed_density_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Pointwise signed generator drift plus the original dividend Stieltjes
    gradient correction remains nonpositive at the actual controlled reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (U : ℝ≥0 × Ω → ℝ)
    (hU : ∀ p, U p =
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1)
    (E : Set (ℝ≥0 × Ω))
    (hE : ∀ p ∈ E, 0 < U p ∧ ENNReal.ofReal (U p) < C)
    (B : Ω → Set ℝ)
    (hB : ∀ ω s, s ∈ B ω →
      0 < riskProcess X x D s.toNNReal ω ∧
        ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C)
    (μ : Measure ℝ≥0) :
    ∀ ω : Ω,
      (∫ t, if (t, ω) ∈ E then
        Real.exp (-(q * (t : ℝ))) *
          (X.generator w (U (t, ω)) - q * w (U (t, ω)))
        else 0 ∂μ) +
      (∫ s, if s ∈ B ω then
        Real.exp (-(q * s)) *
          (1 - deriv w (riskProcess X x D s.toNNReal ω))
        else 0 ∂(dividendMeasure D ω)) ≤ 0 := by
  intro ω
  apply add_nonpos
  · apply integral_nonpos
    intro t
    exact avram_bv_env3_turn26_original_localised_HJB_signed_density_nonpos
      X q hq w C hC hw_gen U E hE (t, ω)
  · apply integral_nonpos
    intro s
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

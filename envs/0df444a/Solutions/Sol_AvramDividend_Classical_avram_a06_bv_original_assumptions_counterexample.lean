-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_bv_original_assumptions_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T15:10:25.142679+00:00
-- url     : https://prove2.me/submissions/73ab6a09-043c-4e9f-a12e-70f5fd99b7a0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a06_bv_zero_cap_conditional_refutation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At zero cap the A06 hypotheses hold for the zero candidate, but the
original expected dividend bound fails at a finite horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ∃ (w : ℝ → ℝ) (C : ℝ≥0∞) (x : ℝ)
      (D : ℝ≥0 → Ω → ℝ) (T : ℝ),
      ContinuousOn w (Ici 0) ∧
      (∀ y < 0, w y = 0) ∧
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) ∧
      ENNReal.ofReal x ≤ C ∧
      IsAdmissibleLe X x C D ∧
      (∀ ω (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω)) ∧
      (∀ ω (t : ℝ≥0),
        (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
            w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) ∧
      0 ≤ T ∧
      ¬ ((∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) := by
  obtain ⟨D, hD, hNoRight, n, hn, hBad⟩ :=
    avram_a06_bv_zero_cap_conditional_refutation X hX hBV hFinite q hq
  refine ⟨(fun _ => 0), 0, 0, D, (n : ℝ),
    ?_, ?_, ?_, ?_, ?_, ?_, hD, ?_, ?_, hn, ?_⟩
  · exact continuousOn_const
  · intro y hy
    rfl
  · exact contDiffOn_const
  · intro y hy hCap
    exact False.elim (not_lt_of_ge
      (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal y) hCap)
  · intro y hy hCap
    exact False.elim (not_lt_of_ge
      (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal y) hCap)
  · simp
  · intro ω t ht hPre
    simp
  · intro ω t ht
    simpa using hNoRight ω t
  · simpa using hBad

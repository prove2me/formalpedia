-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb51_integrable_product_of_integrable_squares
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:08:12.517283+00:00
-- url     : https://prove2.me/submissions/c92b2414-acaa-498e-bd46-b2b132a69ba2

import Mathlib
open MeasureTheory
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false
noncomputable section

/-- An integrable square is sufficient to integrate a mixed product,
provided both real factors are measurably represented. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ)
    (hfmeas : Measurable f) (hgmeas : Measurable g)
    (hf : Integrable (fun ω => f ω ^ 2) μ)
    (hg : Integrable (fun ω => g ω ^ 2) μ) :
    Integrable (fun ω => f ω * g ω) μ := by
  have hsum : Integrable (fun ω => f ω ^ 2 + g ω ^ 2) μ :=
    hf.add hg
  have hdom : ∀ ω, ‖f ω * g ω‖ ≤ ‖f ω ^ 2 + g ω ^ 2‖ := by
    intro ω
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : 0 ≤ f ω ^ 2 + g ω ^ 2)]
    apply abs_le.mpr
    constructor
    · nlinarith [sq_nonneg (f ω + g ω)]
    · nlinarith [sq_nonneg (f ω - g ω)]
  apply hsum.mono' (hfmeas.mul hgmeas).aestronglyMeasurable
  filter_upwards [] with ω
  change ‖f ω * g ω‖ ≤ f ω ^ 2 + g ω ^ 2
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ f ω ^ 2 + g ω ^ 2)] using hdom ω

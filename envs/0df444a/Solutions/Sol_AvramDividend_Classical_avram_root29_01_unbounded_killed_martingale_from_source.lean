-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_unbounded_killed_martingale_from_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:06:34.783346+00:00
-- url     : https://prove2.me/submissions/1f8bd368-8303-4f82-8ce3-67379766755a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_future_window_harmonicity
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_martingale_of_future_window_harmonicity
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Actual original-Lévy downward-killed discounted scale is a true
martingale, based on source-specific conditional future-window harmonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) :
    Martingale (fun t ω =>
      ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) *
          W (x + X.X t ω)) ω) 𝓕 P := by
  obtain ⟨τ, hCover, _⟩ :=
    chat04_explicit_shifted_killed_survival_schedule (0 : ℝ≥0)
  exact chat04_unbounded_killed_martingale_of_future_window_harmonicity
    X hnbv τ hCover q hq W hW x
    (fun s u hsu =>
      avram_root29_01_unbounded_future_window_harmonicity
        X hnbv q hq W hW x s u hsu)

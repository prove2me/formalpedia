-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_bv_killed_scale_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:48:06.396998+00:00
-- url     : https://prove2.me/submissions/71f27f68-d8e0-4a1b-998b-b775341d974b

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_boundedVariation_future_window_killed_scale_harmonicity
import Theorems.Thm_AvramDividend_Classical_chat04_killed_martingale_of_future_window_harmonicity
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

/-- Source-specific true BV downward-killed q-scale martingale from the actual Lévy law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (x : ℝ) :
    Martingale (fun t ω =>
      ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω) 𝓕 P := by
  obtain ⟨τ, hCover, _⟩ :=
    chat04_explicit_shifted_killed_survival_schedule (1 : ℝ≥0)
  exact chat04_killed_martingale_of_future_window_harmonicity
    X hX τ hCover q hq W hW x
    (fun s u hsu =>
      boundedVariation_future_window_killed_scale_harmonicity
        X hX q hq W hW hBV x s u hsu)

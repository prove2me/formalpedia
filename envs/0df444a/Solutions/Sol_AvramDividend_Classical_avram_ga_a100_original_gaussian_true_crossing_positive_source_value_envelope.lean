-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a100_original_gaussian_true_crossing_positive_source_value_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:20:34.099048+00:00
-- url     : https://prove2.me/submissions/9196982d-72e4-446b-a6c7-0aada0d9d2d6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a72_original_gaussian_crossing_cell_clipped_endpoint_eq_stopped_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Original stopped Gaussian crossing-cell positive source error is bounded by the true clipped stopped value displacement and compensator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (H : ℝ)
    (ω : Ω) (n m i : ℕ) (ρ : ℝ≥0)
    (hs : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i : ℝ≥0) * Δ < ρ)
    (hc : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ρ ≤ (i : ℝ≥0) * Δ + Δ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    max (E (v (i + 1)) *
      (w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
        w (Y (v i))) - H) 0 ≤
      |E ρ| * |w (Y s + (X.X ρ ω - X.X s ω)) - w (Y s)| + |H| := by
  obtain ⟨hv0,hv1,_⟩ :=
    avram_ga_a72_original_gaussian_crossing_cell_clipped_endpoint_eq_stopped_source
      X x D ω n m i ρ hs hc
  dsimp only at hv0 hv1
  dsimp only
  rw [hv0, hv1]
  have hSpatial :
      x + X.X ρ ω -
        rightLimit D ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω =
      (x + X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
        rightLimit D ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω) +
      (X.X ρ ω - X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω) := by
    ring
  rw [hSpatial]
  have hSimple (a b : ℝ) : max (a - b) 0 ≤ |a| + |b| := by
    apply max_le
    · linarith [le_abs_self a, neg_le_abs b]
    · linarith [abs_nonneg a, abs_nonneg b]
  simpa only [abs_mul] using
    hSimple
      (Real.exp (-(q * (ρ : ℝ))) *
        (w ((x + X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
          rightLimit D ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω) +
          (X.X ρ ω - X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω)) -
          w (x + X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
            rightLimit D ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω)))
      H

-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb27b_original_stopped_mark_compensator_real_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T16:48:35.898653+00:00
-- url     : https://prove2.me/submissions/33521800-8e23-4f3f-9fd8-248e458f74a5

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva21_original_K_negative_mark_real_time_bridge
import Theorems.Thm_AvramDividend_Classical_avram_bvb26b_real_clock_mapped_positive_mask_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C τ : ℝ≥0∞) (U : ℝ≥0 → ℝ) (w : ℝ → ℝ)
    (q T : ℝ) (n : ℕ) :
    let a : ℝ := T - T / ((n : ℝ) + 2)
    let p : ℝ≥0 → Prop := fun t =>
      (t : ℝ≥0∞) ≤ τ ∧ 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
    let rate : ℝ≥0 → ℝ := fun t =>
      Real.exp (-(q * (t : ℝ))) *
        (∫ z in Set.Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν)
    let J : ℝ≥0 → ℝ := fun t =>
      if 0 < t ∧ (t : ℝ) < a ∧ p t then rate t else 0
    let L : ℝ≥0 → ℝ := fun t =>
      ∫ z : ℝ, (if 0 < t ∧ (t : ℝ) < a ∧
         (t : ℝ≥0∞) ≤ τ ∧ 0 ≤ U t ∧
         ENNReal.ofReal (U t) ≤ C ∧ z < 0 then
         Real.exp (-(q * (t : ℝ))) *
          (w (U t + z) - w (U t)) else 0)
        ∂(X.ν.restrict (Set.Iio (0 : ℝ)))
    let μ : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Set.Icc 0 T)).map Real.toNNReal
    AEStronglyMeasurable J μ →
    (∫ t : ℝ≥0, L t ∂μ) =
      ∫ r in Set.Icc (0 : ℝ) T,
        if 0 < r ∧ r < a ∧ p (Real.toNNReal r)
        then rate (Real.toNNReal r) else 0 := by
  intro a p rate J L μ hMeas
  have hOriginal :=
    (avram_bva21_original_K_negative_mark_real_time_bridge
      X C τ U w q T n) hMeas
  have hClock :=
    avram_bvb26b_real_clock_mapped_positive_mask_eq T a rate p
  calc
    (∫ t : ℝ≥0, L t ∂μ) =
      ∫ r in Set.Icc (0 : ℝ) T,
        if 0 < Real.toNNReal r ∧
           ((Real.toNNReal r : ℝ≥0) : ℝ) < a ∧
           p (Real.toNNReal r)
        then rate (Real.toNNReal r) else 0 := by
          simpa only [L, μ, a, p, rate, J, and_assoc] using hOriginal
    _ = ∫ r in Set.Icc (0 : ℝ) T,
        if 0 < r ∧ r < a ∧ p (Real.toNNReal r)
        then rate (Real.toNNReal r) else 0 := hClock

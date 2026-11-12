-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva21_original_K_negative_mark_real_time_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:04:01.024424+00:00
-- url     : https://prove2.me/submissions/daef8601-fbd0-44ac-8b29-6cb30d2ed185

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva21_negative_mark_restrict_indicator_extract
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_time_map_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Rewrite the physical K compensator as a real-time discounted mark-kernel integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C τ : ℝ≥0∞) (U : ℝ≥0 → ℝ) (w : ℝ → ℝ)
    (q T : ℝ) (n : ℕ) :
    let B : ℝ≥0 → Prop := fun t =>
      0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
      (t : ℝ≥0∞) ≤ τ ∧ 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
    let J : ℝ≥0 → ℝ := fun t =>
      if B t then Real.exp (-(q * (t : ℝ))) *
        (∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν) else 0
    let L : ℝ≥0 → ℝ := fun t =>
      ∫ z : ℝ, (if B t ∧ z < 0 then
        Real.exp (-(q * (t : ℝ))) * (w (U t + z) - w (U t)) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ)))
    AEStronglyMeasurable J
      (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal) →
    (∫ t : ℝ≥0, L t
      ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) =
    ∫ r in Icc (0 : ℝ) T, J (Real.toNNReal r) := by
  intro B J L hMeas
  have hpoint (t : ℝ≥0) : L t = J t := by
    by_cases hb : B t
    · simpa [L, J, hb] using
        (avram_bva21_negative_mark_restrict_indicator_extract
          X.ν (fun z : ℝ => w (U t + z) - w (U t))
          (Real.exp (-(q * (t : ℝ)))) (B t))
    · simp [L, J, hb]
  calc
    (∫ t : ℝ≥0, L t
      ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) =
      (∫ t : ℝ≥0, J t
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∫ r in Icc (0 : ℝ) T, J (Real.toNNReal r) :=
      avram_bvb_b21_original_time_map_integral T J hMeas

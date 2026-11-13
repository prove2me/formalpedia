-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB187_exchange_ae_path_ae_level_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:44:15.058391+00:00
-- url     : https://prove2.me/submissions/66b22537-a79f-45f4-98a1-fe09a22eec44

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB185_ae_level_null_occupation_of_measurable_finite_time_path

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    (Y : Ω → ℝ → ℝ) (hY : ∀ ω, Measurable (Y ω)) (n : ℕ)
    (hOcc : Measurable (fun z : Ω × ℝ =>
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ Y z.1 t = z.2})) :
    ∀ᵐ y ∂(volume : Measure ℝ), ∀ᵐ ω ∂P,
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ Y ω t = y} = 0 := by
  have hFirst : ∀ᵐ ω ∂P, ∀ᵐ y ∂(volume : Measure ℝ),
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ Y ω t = y} = 0 := by
    filter_upwards [] with ω
    exact avram_gbB185_ae_level_null_occupation_of_measurable_finite_time_path
      (Y ω) (hY ω) n
  have hMeas : MeasurableSet {z : Ω × ℝ |
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ Y z.1 t = z.2} = 0} := by
    exact hOcc (measurableSet_singleton (0 : ℝ≥0∞))
  exact (Measure.ae_ae_comm hMeas).mp hFirst

-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb101_bounded_joint_integral_time_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:27:09.903742+00:00
-- url     : https://prove2.me/submissions/4a543882-708d-43b6-a5ad-d8ca2df6d515

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (T : ℝ) (f : ℝ → Ω → ℝ)
    (hf : StronglyMeasurable (fun z : ℝ × Ω => f z.1 z.2))
    (hInt : ∀ t, Integrable (f t) P)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ t ω, ‖f t ω‖ ≤ B) :
    IntegrableOn (fun t => ∫ ω, f t ω ∂P)
      (Ioo (0 : ℝ) T) volume := by
  have hfinite : volume (Ioo (0 : ℝ) T) < ⊤ := by
    simp
  have hsm : StronglyMeasurable
      (fun t => ∫ ω, f t ω ∂P) := hf.integral_prod_right
  apply IntegrableOn.of_bound hfinite hsm.aestronglyMeasurable
    (∫ _ : Ω, B ∂P)
  filter_upwards [] with t
  calc
    ‖∫ ω, f t ω ∂P‖ ≤ ∫ ω, ‖f t ω‖ ∂P :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _ : Ω, B ∂P :=
      integral_mono (hInt t).norm (integrable_const _)
        (fun ω => hB t ω)

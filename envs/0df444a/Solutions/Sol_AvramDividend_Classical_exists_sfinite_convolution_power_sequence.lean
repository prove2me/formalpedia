-- Prove2me | solution 1 for AvramDividend.Classical.exists_sfinite_convolution_power_sequence
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T21:56:13.117821+00:00
-- url     : https://prove2.me/submissions/ba90addd-8826-4388-820d-bf0a7cbc6edf

import Mathlib
open MeasureTheory

theorem solution
    (κ : Measure ℝ) [SFinite κ] :
    ∃ m : ℕ → Measure ℝ,
      m 0 = Measure.dirac 0 ∧
      (∀ n : ℕ, m (n + 1) = Measure.conv κ (m n)) ∧
      (∀ n : ℕ, SFinite (m n)) := by
  refine ⟨fun n => Nat.rec (motive := fun _ => Measure ℝ) (Measure.dirac 0)
    (fun _ m => Measure.conv κ m) n, rfl, fun n => rfl, ?_⟩
  intro n
  induction n with
  | zero =>
    show SFinite (Measure.dirac (0 : ℝ))
    infer_instance
  | succ n ih =>
    show SFinite (Measure.conv κ _)
    infer_instance

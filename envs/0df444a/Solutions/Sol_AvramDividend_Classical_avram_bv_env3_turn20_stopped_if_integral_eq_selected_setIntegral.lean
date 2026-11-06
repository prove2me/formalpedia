-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn20_stopped_if_integral_eq_selected_setIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:55:45.520592+00:00
-- url     : https://prove2.me/submissions/4d019908-8f7b-47b8-ad7f-e885b9e2f38c

import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

/-- The actual stopped physical-grid if-mask integrates on its selection event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (k : Ω → ℕ) (hk : Measurable k)
    (i : ℕ) (M : Ω → ℝ) :
    (∫ ω, (if i < k ω then M ω else 0) ∂P) =
      (∫ ω in {ω : Ω | i < k ω}, M ω ∂P) := by
  have hs : MeasurableSet {ω : Ω | i < k ω} :=
    measurableSet_lt measurable_const hk
  have hMask : (fun ω : Ω => if i < k ω then M ω else 0) =
      ({ω : Ω | i < k ω}.indicator M) := by
    funext ω
    by_cases h : i < k ω <;> simp [Set.indicator_apply, h]
  rw [hMask]
  exact integral_indicator hs

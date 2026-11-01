-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_actual_source_future_grid_deficit_count_indep_past
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:42:03.012878+00:00
-- url     : https://prove2.me/submissions/008b0b85-8b84-474d-886b-f54365595245

import Mathlib.MeasureTheory.Group.Arithmetic
import Theorems.Thm_AvramDividend_Classical_actual_levy_past_indep_measurable_future_jump_family_ws01b
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal BigOperators

/-! Actual source future finite-grid drift-deficit counts are independent of the original past. -/
theorem solution
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (n : ℕ) (grid : ℕ → ℝ≥0) :
    IndepFun H (fun ω : Ω =>
      ((Finset.range n).filter (fun i =>
        (X.X (s + grid (i + 1)) ω - X.X s ω) -
          (X.X (s + grid i) ω - X.X s ω) <
          X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ)))).card) P := by
  classical
  let q : ℕ → (ℝ≥0 → ℝ) → Prop := fun i f =>
    f (grid (i + 1)) - f (grid i) <
      X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ))
  have hq (i : ℕ) : MeasurableSet {f : ℝ≥0 → ℝ | q i f} := by
    have hl : Measurable (fun f : ℝ≥0 → ℝ => f (grid i)) :=
      measurable_pi_apply (grid i)
    have hr : Measurable (fun f : ℝ≥0 → ℝ => f (grid (i + 1))) :=
      measurable_pi_apply (grid (i + 1))
    exact measurableSet_lt (hr.sub hl) measurable_const
  have hSum : Measurable (fun f : ℝ≥0 → ℝ =>
      ∑ i ∈ Finset.range n, if q i f then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (hq i) measurable_const measurable_const
  have hEq :
      (fun f : ℝ≥0 → ℝ => ((Finset.range n).filter (fun i => q i f)).card) =
      (fun f : ℝ≥0 → ℝ =>
        ∑ i ∈ Finset.range n, if q i f then (1 : ℕ) else 0) := by
    funext f
    exact Finset.card_filter (fun i => q i f) (Finset.range n)
  have hF : Measurable (fun f : ℝ≥0 → ℝ =>
      ((Finset.range n).filter (fun i => q i f)).card) := by
    rw [hEq]
    exact hSum
  let Fpath : (ℝ≥0 → ℝ) → ℕ := fun f =>
    ((Finset.range n).filter (fun i => q i f)).card
  have hInd : IndepFun H
      (fun ω : Ω => Fpath (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) P :=
    actual_levy_past_indep_measurable_future_jump_family_ws01b
      X s H hH Fpath hF
  simpa only [Fpath, q] using hInd

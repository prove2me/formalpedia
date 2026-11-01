-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave4_04a_actual_source_future_grid_deficit_count_indep_past
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:43:14.699721+00:00
-- url     : https://prove2.me/submissions/be664720-8c71-4dcc-a5db-ff3a7ebbd318

import Theorems.Thm_AvramDividend_Classical_actual_levy_past_indep_measurable_future_jump_family_ws01b
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal BigOperators

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
  let p : ℕ → (ℝ≥0 → ℝ) → Prop := fun i Y =>
    Y (grid (i + 1)) - Y (grid i) <
      X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ))
  have hp (i : ℕ) : MeasurableSet {Y : ℝ≥0 → ℝ | p i Y} := by
    exact measurableSet_lt
      ((measurable_pi_apply (grid (i + 1))).sub (measurable_pi_apply (grid i)))
      measurable_const
  have hSum : Measurable (fun Y : ℝ≥0 → ℝ =>
      ∑ i ∈ Finset.range n, if p i Y then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (hp i) measurable_const measurable_const
  have hEq :
      (fun Y : ℝ≥0 → ℝ => ((Finset.range n).filter (fun i => p i Y)).card) =
      (fun Y : ℝ≥0 → ℝ =>
        ∑ i ∈ Finset.range n, if p i Y then (1 : ℕ) else 0) := by
    funext Y
    exact Finset.card_filter (fun i => p i Y) (Finset.range n)
  let Fpath : (ℝ≥0 → ℝ) → ℕ := fun Y =>
    ((Finset.range n).filter (fun i => p i Y)).card
  have hF : Measurable Fpath := by
    change Measurable (fun Y : ℝ≥0 → ℝ =>
      ((Finset.range n).filter (fun i => p i Y)).card)
    rw [hEq]
    exact hSum
  change IndepFun H
    (fun ω : Ω => Fpath (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) P
  exact actual_levy_past_indep_measurable_future_jump_family_ws01b
    X s H hH Fpath hF

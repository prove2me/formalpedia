-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_actual_original_grid_drift_deficit_count_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:34:20.985363+00:00
-- url     : https://prove2.me/submissions/375850fa-310f-4cc3-94b5-8c3d14d3d727

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (grid : ℕ → ℝ≥0) :
    Measurable (fun ω : Ω =>
      ((Finset.range n).filter (fun i =>
        X.X (grid (i + 1)) ω - X.X (grid i) ω <
          X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ)))).card) := by
  classical
  let p : ℕ → Ω → Prop := fun i ω =>
    X.X (grid (i + 1)) ω - X.X (grid i) ω <
      X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ))
  have hp (i : ℕ) : MeasurableSet {ω : Ω | p i ω} := by
    have hleft : Measurable (fun ω : Ω => X.X (grid i) ω) :=
      (X.adapted (grid i)).mono (𝓕.le (grid i)) le_rfl
    have hright : Measurable (fun ω : Ω => X.X (grid (i + 1)) ω) :=
      (X.adapted (grid (i + 1))).mono (𝓕.le (grid (i + 1))) le_rfl
    exact measurableSet_lt (hright.sub hleft) measurable_const
  have hSum : Measurable (fun ω : Ω =>
      ∑ i ∈ Finset.range n, if p i ω then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (hp i) measurable_const measurable_const
  have hEq :
      (fun ω : Ω =>
        ((Finset.range n).filter (fun i => p i ω)).card) =
      (fun ω : Ω =>
        ∑ i ∈ Finset.range n, if p i ω then (1 : ℕ) else 0) := by
    funext ω
    exact Finset.card_filter (fun i => p i ω) (Finset.range n)
  change Measurable (fun ω : Ω =>
    ((Finset.range n).filter (fun i => p i ω)).card)
  rw [hEq]
  exact hSum

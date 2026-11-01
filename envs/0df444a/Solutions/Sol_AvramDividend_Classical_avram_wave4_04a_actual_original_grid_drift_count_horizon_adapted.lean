-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_actual_original_grid_drift_count_horizon_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:22:38.149443+00:00
-- url     : https://prove2.me/submissions/15f8dfe1-f6fd-4c37-8ef1-0d6375eab574

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! Actual Lévy grid drift-deficit counts are measurable in their source filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (grid : ℕ → ℝ≥0)
    (hBound : ∀ i : ℕ, i ≤ n → grid i ≤ T) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ((Finset.range n).filter (fun i =>
        X.X (grid (i + 1)) ω - X.X (grid i) ω <
          X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ)))).card) := by
  classical
  let p : ℕ → Ω → Prop := fun i ω =>
    X.X (grid (i + 1)) ω - X.X (grid i) ω <
      X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ))
  have hp (i : ℕ) (hi : i < n) : MeasurableSet[𝓕 T] {ω : Ω | p i ω} := by
    have hleft : Measurable[𝓕 T] (fun ω : Ω => X.X (grid i) ω) :=
      (X.adapted (grid i)).mono (𝓕.mono (hBound i (Nat.le_of_lt hi))) le_rfl
    have hright : Measurable[𝓕 T] (fun ω : Ω => X.X (grid (i + 1)) ω) :=
      (X.adapted (grid (i + 1))).mono
        (𝓕.mono (hBound (i + 1) (Nat.succ_le_of_lt hi))) le_rfl
    exact measurableSet_lt (hright.sub hleft) measurable_const
  have hSum : Measurable[𝓕 T] (fun ω : Ω =>
      ∑ i ∈ Finset.range n, if p i ω then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (hp i (Finset.mem_range.mp hi))
      measurable_const measurable_const
  have hEq :
      (fun ω : Ω => ((Finset.range n).filter (fun i => p i ω)).card) =
      (fun ω : Ω => ∑ i ∈ Finset.range n, if p i ω then (1 : ℕ) else 0) := by
    funext ω
    exact Finset.card_filter (fun i => p i ω) (Finset.range n)
  change Measurable[𝓕 T] (fun ω : Ω =>
    ((Finset.range n).filter (fun i => p i ω)).card)
  rw [hEq]
  exact hSum

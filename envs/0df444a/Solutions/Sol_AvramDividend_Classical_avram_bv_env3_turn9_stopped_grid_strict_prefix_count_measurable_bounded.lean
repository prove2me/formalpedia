-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn9_stopped_grid_strict_prefix_count_measurable_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:00:57.030302+00:00
-- url     : https://prove2.me/submissions/1c209a2c-78de-4b84-b0df-bf0baa7b6c9c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The physical-grid count of pre-ruin strict right endpoints is a bounded
measurable selector. The strict inequality excludes the ruin contact atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (m : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let K : Ω → ℕ := fun ω =>
      ∑ j ∈ Finset.range m,
        if (((j + 1 : ℕ) : ℝ≥0) *
          (T / ((m + 1 : ℕ) : ℝ≥0)) < τ ω)
        then 1 else 0
    Measurable K ∧ ∀ ω, K ω ≤ m := by
  dsimp
  have hτ : Measurable (fun ω : Ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) := by
    exact ENNReal.measurable_toNNReal.comp
      ((ruinTime_measurable X x D hD.1.1).min measurable_const)
  constructor
  · classical
    apply Finset.measurable_sum
    intro j hj
    have hs : MeasurableSet {ω : Ω |
        (((j + 1 : ℕ) : ℝ≥0) *
          (T / ((m + 1 : ℕ) : ℝ≥0))) <
          (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal} :=
      measurableSet_lt measurable_const hτ
    exact Measurable.ite hs measurable_const measurable_const
  · intro ω
    calc
      (∑ j ∈ Finset.range m,
        if (((j + 1 : ℕ) : ℝ≥0) *
          (T / ((m + 1 : ℕ) : ℝ≥0))) <
          (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
        then (1 : ℕ) else 0) ≤
        ∑ j ∈ Finset.range m, (1 : ℕ) := by
          apply Finset.sum_le_sum
          intro j hj
          split_ifs <;> omega
      _ = m := by simp

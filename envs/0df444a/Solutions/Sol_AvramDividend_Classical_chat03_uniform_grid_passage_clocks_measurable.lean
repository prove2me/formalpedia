-- Prove2me | solution 1 for AvramDividend.Classical.chat03_uniform_grid_passage_clocks_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:53:57.653781+00:00
-- url     : https://prove2.me/submissions/fe00e31e-7ec9-45f1-b07d-2d6141254b74

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-!
Each exact uniform-grid strict passage clock is measurable as an
ENNReal-valued random variable, including an empty grid crossing set.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) (h : ℝ≥0) :
    Measurable (fun ω : Ω => ⨅ k : ℕ,
      if upper < X.X ((k : ℝ≥0) * h) ω then
        (((k : ℝ≥0) * h) : ℝ≥0∞) else ∞) ∧
    Measurable (fun ω : Ω => ⨅ k : ℕ,
      if X.X ((k : ℝ≥0) * h) ω < lower then
        (((k : ℝ≥0) * h) : ℝ≥0∞) else ∞) := by
  constructor
  · apply Measurable.iInf
    intro k
    have hZ : Measurable (X.X ((k : ℝ≥0) * h)) :=
      (X.adapted _).mono (𝓕.le _) le_rfl
    have hSet : MeasurableSet
        {ω : Ω | upper < X.X ((k : ℝ≥0) * h) ω} :=
      measurableSet_lt measurable_const hZ
    exact measurable_const.ite hSet measurable_const
  · apply Measurable.iInf
    intro k
    have hZ : Measurable (X.X ((k : ℝ≥0) * h)) :=
      (X.adapted _).mono (𝓕.le _) le_rfl
    have hSet : MeasurableSet
        {ω : Ω | X.X ((k : ℝ≥0) * h) ω < lower} :=
      measurableSet_lt hZ measurable_const
    exact measurable_const.ite hSet measurable_const

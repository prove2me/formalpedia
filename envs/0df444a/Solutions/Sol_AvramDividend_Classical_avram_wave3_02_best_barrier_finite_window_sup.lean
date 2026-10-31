-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_best_barrier_finite_window_sup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:56:02.551685+00:00
-- url     : https://prove2.me/submissions/cde6767b-203e-4b1e-a8fd-a639f20f8a66

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_high_barrier_eventually_worse_than_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The best true constant-barrier dividend value for any fixed positive
reserve can be computed over some finite cap interval [0,A]. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) :
    ∃ A : ℝ, 0 ≤ A ∧
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
        dividendValue X q x (barrierStrategy X x a)) =
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a ∧ a ≤ A),
        dividendValue X q x (barrierStrategy X x a)) := by
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.1
    (avram_wave3_02_high_barrier_eventually_worse_than_zero
      X hX q hq W hW x hx)
  let B : ℝ := max A 0
  have hB : 0 ≤ B := le_max_right _ _
  have hzero :
      dividendValue X q x (barrierStrategy X x 0) ≤
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a ∧ a ≤ B),
        dividendValue X q x (barrierStrategy X x a)) := by
    exact le_iSup_of_le (0 : ℝ)
      (le_iSup_of_le ⟨le_refl (0 : ℝ), hB⟩ (le_refl _))
  refine ⟨B, hB, ?_⟩
  apply le_antisymm
  · refine iSup_le fun a => ?_
    refine iSup_le fun ha => ?_
    by_cases hab : a ≤ B
    · exact le_iSup_of_le a
        (le_iSup_of_le ⟨ha, hab⟩ (le_refl _))
    · have hBa : B < a := lt_of_not_ge hab
      have hAa : A ≤ a := (le_max_left A 0).trans (le_of_lt hBa)
      exact (le_of_lt (hA a hAa)).trans hzero
  · refine iSup_le fun a => ?_
    refine iSup_le fun ha => ?_
    exact le_iSup_of_le a
      (le_iSup_of_le ha.1 (le_refl _))

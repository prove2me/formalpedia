-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_uniform_interval_finite_barrier_window
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:45:14.998114+00:00
-- url     : https://prove2.me/submissions/d59ff8b1-31ed-4dc3-8c41-bdfa8fc10d9a

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_capital_interval_high_barrier_dominated

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- One bounded barrier-optimisation window works at all initial
reserves in any compact interval separated from zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (δ R : ℝ) (hδ : 0 < δ) (hδR : δ ≤ R) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, δ ≤ x → x ≤ R →
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
        dividendValue X q x (barrierStrategy X x a)) =
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a ∧ a ≤ A),
        dividendValue X q x (barrierStrategy X x a)) := by
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.1
    (avram_wave3_02_uniform_capital_interval_high_barrier_dominated
      X hX q hq W hW δ R hδ hδR)
  let B : ℝ := max A 0
  have hB : 0 ≤ B := le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro x hδx hxR
  have hzero :
      dividendValue X q x (barrierStrategy X x 0) ≤
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a ∧ a ≤ B),
        dividendValue X q x (barrierStrategy X x a)) := by
    exact le_iSup_of_le (0 : ℝ)
      (le_iSup_of_le ⟨le_refl (0 : ℝ), hB⟩ (le_refl _))
  apply le_antisymm
  · refine iSup_le fun a => ?_
    refine iSup_le fun ha => ?_
    by_cases hab : a ≤ B
    · exact le_iSup_of_le a
        (le_iSup_of_le ⟨ha, hab⟩ (le_refl _))
    · have hBa : B < a := lt_of_not_ge hab
      have hAa : A ≤ a := (le_max_left A 0).trans (le_of_lt hBa)
      exact (le_of_lt (hA a hAa x hδx hxR)).trans hzero
  · refine iSup_le fun a => ?_
    refine iSup_le fun ha => ?_
    exact le_iSup_of_le a
      (le_iSup_of_le ha.1 (le_refl _))

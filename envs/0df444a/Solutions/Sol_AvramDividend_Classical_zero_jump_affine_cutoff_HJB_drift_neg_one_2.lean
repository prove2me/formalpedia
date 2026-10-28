-- Prove2me | solution 2 for AvramDividend.Classical.zero_jump_affine_cutoff_HJB_drift_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:35:16.029519+00:00
-- url     : https://prove2.me/submissions/d463a6c8-e066-442f-9494-70547ab83300

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_affine_cutoff_deriv_eq_one_positive
import Theorems.Thm_AvramDividend_Classical_zero_jump_affine_cutoff_generator_eq_drift
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (hc : X.c = -1)
    (y : ℝ) (hy : 0 < y) :
    X.GeneratorIntegrable (fun z : ℝ => if z < 0 then 0 else z - 1) y ∧
      X.generator (fun z : ℝ => if z < 0 then 0 else z - 1) y - (fun z : ℝ => if z < 0 then 0 else z - 1) y ≤ 0 ∧
      1 ≤ deriv (fun z : ℝ => if z < 0 then 0 else z - 1) y := by
  obtain ⟨hI, hg⟩ := zero_jump_affine_cutoff_generator_eq_drift X hν y hy
  have hd := affine_cutoff_deriv_eq_one_positive y hy
  refine ⟨hI, ?_, ?_⟩
  · rw [hg]
    have hn : ¬ y < 0 := not_lt.mpr (le_of_lt hy)
    simp only [if_neg hn]
    rw [hc]
    linarith
  · rw [hd]

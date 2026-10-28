-- Prove2me | solution 1 for AvramDividend.Classical.zero_jump_affine_cutoff_HJB_drift_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:35:05.849539+00:00
-- url     : https://prove2.me/submissions/5972690e-9ec5-4eac-a271-f7269f1e35d3

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_affine_cutoff_deriv_eq_one_positive
import Theorems.Thm_AvramDividend_Classical_zero_jump_affine_cutoff_generator_eq_drift
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
  obtain ⟨h1, h2⟩ := zero_jump_affine_cutoff_generator_eq_drift X hν y hy
  refine ⟨h1, ?_, (affine_cutoff_deriv_eq_one_positive y hy).ge⟩
  rw [h2, hc]
  simp only [not_lt.mpr hy.le, if_false]
  linarith

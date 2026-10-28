-- Prove2me | solution 1 for AvramDividend.Classical.zero_jump_affine_generator_eq_drift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:14:56.799994+00:00
-- url     : https://prove2.me/submissions/7624cebf-0d82-4963-b9f7-19619570c0f9

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (x : ℝ) :
    X.GeneratorIntegrable (fun z : ℝ => z - 1) x ∧
      X.generator (fun z : ℝ => z - 1) x = X.c := by
  have hd : deriv (fun z : ℝ => z - 1) = fun _ => 1 := by
    funext z; simp
  have h2 : iteratedDeriv 2 (fun z : ℝ => z - 1) x = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd]; simp
  refine ⟨?_, ?_⟩
  · unfold SpectrallyNegativeLevy.GeneratorIntegrable; rw [hν]; simp [IntegrableOn]
  · unfold SpectrallyNegativeLevy.generator; rw [hν, h2, hd]; simp

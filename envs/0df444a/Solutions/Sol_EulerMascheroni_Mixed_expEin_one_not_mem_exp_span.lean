-- Prove2me | solution 1 for EulerMascheroni.Mixed.expEin_one_not_mem_exp_span
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T22:42:19.393728+00:00
-- url     : https://prove2.me/submissions/7d032f9a-c5ef-4d7c-8980-9f601eb07270
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_eulerMascheroni_mixedCover
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Algebraic.Integral
import Theorems.Thm_EulerMascheroni_Mixed_exp_one_expEin_one_algebraicIndependent

open Algebra in
theorem solution (α β : ℝ)
    (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β) :
    EulerMascheroni.Mixed.expEin 1 ≠ (α : ℂ) + (β : ℂ) * Complex.exp 1 := by
  intro h
  have hx := EulerMascheroni.Mixed.exp_one_expEin_one_algebraicIndependent
  have ht := hx.transcendental_adjoin (s := {0}) (i := 1) (by decide)
  set S := Algebra.adjoin ℚ (![Complex.exp 1, EulerMascheroni.Mixed.expEin 1] '' {0})
  have hinj : Function.Injective (algebraMap ℚ S) := (algebraMap ℚ S).injective
  have hαC : IsAlgebraic ℚ (α : ℂ) := hα.algebraMap (A := ℂ)
  have hβC : IsAlgebraic ℚ (β : ℂ) := hβ.algebraMap (A := ℂ)
  have he : IsAlgebraic S (Complex.exp 1) := by
    have hmem : Complex.exp 1 ∈ S := Algebra.subset_adjoin ⟨0, rfl, rfl⟩
    exact isAlgebraic_algebraMap (⟨_, hmem⟩ : S)
  apply ht
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [h]
  exact (hαC.extendScalars hinj).add ((hβC.extendScalars hinj).mul he)

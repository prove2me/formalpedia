-- Prove2me | solution 1 for Esquisse.galois_orbit_of_polynomial_finite
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T00:06:49.185097+00:00
-- url     : https://prove2.me/submissions/c736e568-1468-4813-bd95-e94400e00d63

import Definitions.Def_esquisse_dessins_basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.Data.Finite.Prod

open Polynomial
open Esquisse

private theorem coefficient_orbit_finite (a : AlgNum) :
    (Set.range (fun γ : GaloisQ => γ a)).Finite := by
  classical
  letI : Algebra.IsAlgebraic ℚ AlgNum := AlgebraicClosure.isAlgebraic ℚ
  have ha : IsIntegral ℚ a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  have hne : (minpoly ℚ a).map (algebraMap ℚ AlgNum) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ AlgNum).injective).mpr (minpoly.ne_zero ha)
  apply (Polynomial.finite_setOfPred_isRoot hne).subset
  rintro b ⟨γ, rfl⟩
  change ((minpoly ℚ a).map (algebraMap ℚ AlgNum)).eval (γ a) = 0
  rw [Polynomial.eval_map_algebraMap]
  exact minpoly.aeval_algHom ℚ γ.toAlgHom a

theorem solution (P : Polynomial AlgNum) :
    (Set.range (fun γ : GaloisQ => galoisConj γ P)).Finite := by
  classical
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      apply ((hP.prod hQ).image (fun z : Polynomial AlgNum × Polynomial AlgNum => z.1 + z.2)).subset
      rintro R ⟨γ, rfl⟩
      exact ⟨(galoisConj γ P, galoisConj γ Q), ⟨⟨γ, rfl⟩, ⟨γ, rfl⟩⟩,
        by simp [galoisConj]⟩
  | monomial n a =>
      apply ((coefficient_orbit_finite a).image (fun b : AlgNum => monomial n b)).subset
      rintro R ⟨γ, rfl⟩
      exact ⟨γ a, ⟨γ, rfl⟩, by simp [galoisConj]⟩

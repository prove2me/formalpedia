-- Prove2me | solution 1 for EinsteinFieldEquationsD.minkowski_vacuum_solution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T07:22:50.630988+00:00
-- url     : https://prove2.me/submissions/fb4097b3-8853-4e2d-b1b5-3e7a8df45b14

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_EinsteinFieldEquationsD_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open EinsteinFieldEquationsD

theorem solution (κ : ℝ) :
    IsMetricOn minkowskiMetric Set.univ ∧
      (∀ x : Coord 4, ∀ a b : Fin 4, ricci minkowskiMetric x a b = 0) ∧
      EinsteinFieldEquationsOn minkowskiMetric 0 0 κ Set.univ := by
  classical
  have hmet : IsMetricOn minkowskiMetric Set.univ := by
    refine ⟨isOpen_univ, ?_, ?_, ?_⟩
    · intro a b
      change ContDiffOn ℝ (⊤ : ℕ∞)
        (fun _ : Coord 4 =>
          (Matrix.diagonal ![-1, (1 : ℝ), 1, 1]) a b) Set.univ
      exact contDiffOn_const
    · intro x hx a b
      change (Matrix.diagonal ![-1, (1 : ℝ), 1, 1]) a b =
        (Matrix.diagonal ![-1, (1 : ℝ), 1, 1]) b a
      by_cases hab : a = b
      · subst b
        rfl
      · simp [Matrix.diagonal_apply, hab, Ne.symm hab]
    · intro x hx
      change (Matrix.diagonal ![-1, (1 : ℝ), 1, 1] :
        Matrix (Fin 4) (Fin 4) ℝ).det ≠ 0
      norm_num [Matrix.det_diagonal, Fin.prod_univ_succ]
  have hpart (l a b : Fin 4) (x : Coord 4) :
      partialDeriv l (fun y => minkowskiMetric y a b) x = 0 := by
    simp [partialDeriv, minkowskiMetric]
  have hΓ (x : Coord 4) (m a b : Fin 4) :
      christoffel minkowskiMetric x m a b = 0 := by
    simp [christoffel, hpart]
  have hΓfun (m a b : Fin 4) :
      (fun y : Coord 4 => christoffel minkowskiMetric y m a b) =
        (fun _ => 0) := by
    funext y
    exact hΓ y m a b
  have hpartΓ (l m a b : Fin 4) (x : Coord 4) :
      partialDeriv l (fun y => christoffel minkowskiMetric y m a b) x = 0 := by
    rw [hΓfun m a b]
    simp [partialDeriv]
  have hRiem (x : Coord 4) (m a b c : Fin 4) :
      riemann minkowskiMetric x m a b c = 0 := by
    simp [riemann, hpartΓ, hΓ, partialDeriv]
  have hRic (x : Coord 4) (a b : Fin 4) :
      ricci minkowskiMetric x a b = 0 := by
    simp [ricci, hRiem]
  refine ⟨hmet, hRic, ?_⟩
  intro x hx a b
  change einsteinTensor minkowskiMetric x a b +
    0 * minkowskiMetric x a b = κ * (0 : Tensor2 4) x a b
  have hscalar : scalarCurvature minkowskiMetric x = 0 := by
    simp [scalarCurvature, hRic]
  simp [einsteinTensor, hRic, hscalar]

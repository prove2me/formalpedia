-- Prove2me | solution 1 for D1Bound5.finiteA5_root_coeff_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:40:54.461851+00:00
-- url     : https://prove2.me/submissions/3acd37ec-c205-4755-91ee-68de49f117df

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteA5Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteA5Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions

section
namespace D1Bound5

















private theorem finiteA5_root_coeff_00 {R : Type*} [CommRing R]
    (x y c : R) :
    ![finiteA5Left x y c 0,finiteA5Right x y c 0] 0 =
      ∑ ell : Fin 6, finiteA5RootCoeff x y 0 0 ell*c^(ell : ℕ) := by
  norm_num [finiteA5Left,finiteA5Right,finiteA5RootCoeff,
    finiteA5Coeff0,finiteA5Coeff1,finiteA5Coeff2,finiteA5Coeff3,finiteA5Coeff4,finiteA5Coeff5,
    finiteHomogeneousTwo,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  <;> ring

private theorem finiteA5_root_coeff_01 {R : Type*} [CommRing R]
    (x y c : R) :
    ![finiteA5Left x y c 0,finiteA5Right x y c 0] 1 =
      ∑ ell : Fin 6, finiteA5RootCoeff x y 0 1 ell*c^(ell : ℕ) := by
  norm_num [finiteA5Left,finiteA5Right,finiteA5RootCoeff,
    finiteA5Coeff0,finiteA5Coeff1,finiteA5Coeff2,finiteA5Coeff3,finiteA5Coeff4,finiteA5Coeff5,
    finiteHomogeneousTwo,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  <;> ring

private theorem finiteA5_root_coeff_10 {R : Type*} [CommRing R]
    (x y c : R) :
    ![finiteA5Left x y c 1,finiteA5Right x y c 1] 0 =
      ∑ ell : Fin 6, finiteA5RootCoeff x y 1 0 ell*c^(ell : ℕ) := by
  norm_num [finiteA5Left,finiteA5Right,finiteA5RootCoeff,
    finiteA5Coeff0,finiteA5Coeff1,finiteA5Coeff2,finiteA5Coeff3,finiteA5Coeff4,finiteA5Coeff5,
    finiteHomogeneousTwo,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  <;> ring

private theorem finiteA5_root_coeff_11 {R : Type*} [CommRing R]
    (x y c : R) :
    ![finiteA5Left x y c 1,finiteA5Right x y c 1] 1 =
      ∑ ell : Fin 6, finiteA5RootCoeff x y 1 1 ell*c^(ell : ℕ) := by
  norm_num [finiteA5Left,finiteA5Right,finiteA5RootCoeff,
    finiteA5Coeff0,finiteA5Coeff1,finiteA5Coeff2,finiteA5Coeff3,finiteA5Coeff4,finiteA5Coeff5,
    finiteHomogeneousTwo,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  <;> ring

private theorem finiteA5_root_coeff_20 {R : Type*} [CommRing R]
    (x y c : R) :
    ![finiteA5Left x y c 2,finiteA5Right x y c 2] 0 =
      ∑ ell : Fin 6, finiteA5RootCoeff x y 2 0 ell*c^(ell : ℕ) := by
  norm_num [finiteA5Left,finiteA5Right,finiteA5RootCoeff,
    finiteA5Coeff0,finiteA5Coeff1,finiteA5Coeff2,finiteA5Coeff3,finiteA5Coeff4,finiteA5Coeff5,
    finiteHomogeneousTwo,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  <;> ring

private theorem finiteA5_root_coeff_21 {R : Type*} [CommRing R]
    (x y c : R) :
    ![finiteA5Left x y c 2,finiteA5Right x y c 2] 1 =
      ∑ ell : Fin 6, finiteA5RootCoeff x y 2 1 ell*c^(ell : ℕ) := by
  norm_num [finiteA5Left,finiteA5Right,finiteA5RootCoeff,
    finiteA5Coeff0,finiteA5Coeff1,finiteA5Coeff2,finiteA5Coeff3,finiteA5Coeff4,finiteA5Coeff5,
    finiteHomogeneousTwo,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  <;> ring

theorem _root_.solution {R : Type*} [CommRing R]
    (x y c : R) (i : Fin 3) (j : Fin 2) :
    ![finiteA5Left x y c i,finiteA5Right x y c i] j =
      ∑ ell : Fin 6, finiteA5RootCoeff x y i j ell*c^(ell : ℕ) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl
  · exact finiteA5_root_coeff_00 x y c
  · exact finiteA5_root_coeff_01 x y c
  · exact finiteA5_root_coeff_10 x y c
  · exact finiteA5_root_coeff_11 x y c
  · exact finiteA5_root_coeff_20 x y c
  · exact finiteA5_root_coeff_21 x y c
















end D1Bound5
end

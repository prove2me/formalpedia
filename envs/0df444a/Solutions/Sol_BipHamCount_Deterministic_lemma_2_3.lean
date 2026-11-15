-- Prove2me | solution 1 for BipHamCount.Deterministic.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-14T13:42:29.268382+00:00
-- url     : https://prove2.me/submissions/225e18bc-a47e-45a1-8cf0-da49603b9c92

import Definitions.Def_BipHamCount_Deterministic_Core
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Reindex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open Matrix BipHamCount.Deterministic

private lemma det_piecewise {R K : Type*} [CommRing R] [Fintype K] [DecidableEq K]
    (C : Matrix K K R) (d : K → R) (I : Finset K) :
    det (Matrix.of (I.piecewise C.row (diagonal d).row)) = (C.submatrix (↑) (↑) : Matrix I I R).det * ∏ i ∈ Iᶜ, d i := by
  classical
  let e := Equiv.sumCompl (fun k => k ∈ I)
  let A : Matrix K K R := Matrix.of (I.piecewise C.row (diagonal d).row)
  rw [← Matrix.det_submatrix_equiv_self e A]
  have h : A.submatrix e e = Matrix.fromBlocks
      (C.submatrix Subtype.val Subtype.val : Matrix I I R)
      (C.submatrix Subtype.val Subtype.val : Matrix I {k // k ∉ I} R)
      0 (diagonal fun k : {k // k ∉ I} => d k.1) := by
    ext (i | i) (j | j) <;> dsimp [A, e]
    · simp [Finset.piecewise]
    · simp [Finset.piecewise]
    · simp only [Finset.piecewise, if_neg i.prop]
      exact Matrix.diagonal_apply_ne d (fun h => i.prop (h ▸ j.prop))
    · simp [Finset.piecewise, i.prop, Matrix.diagonal_apply, Subtype.ext_iff, Pi.single_apply, eq_comm]
  rw [h, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal]
  congr 1
  exact (Finset.prod_subtype Iᶜ (by simp) d).symm

private lemma ordered_minor {R K : Type*} [CommRing R] [LinearOrder K]
    (C : Matrix K K R) (I : Finset K) :
    minor C I I = (C.submatrix (↑) (↑) : Matrix I I R).det := by
  classical
  unfold minor
  rw [dif_pos rfl]
  unfold squareSub
  let e : Fin I.card ≃ I := (I.orderIsoOfFin rfl).toEquiv
  have he : C.submatrix (I.orderEmbOfFin rfl) (I.orderEmbOfFin rfl) =
      (C.submatrix (↑) (↑) : Matrix I I R).submatrix e e := by rfl
  rw [he, Matrix.det_submatrix_equiv_self]

theorem solution {R K : Type*} [CommRing R] [Fintype K] [LinearOrder K]
    (C : Matrix K K R) (d : K → R) :
    (Matrix.diagonal d + C).det = ∑ I ∈ (Finset.univ : Finset K).powerset,
      minor C I I * ∏ i ∈ Iᶜ, d i := by
  classical
  let D := (detRowAlternating : (K → R) [⋀^K]→ₗ[R] R)
  rw [add_comm]
  change D (C.row + (Matrix.diagonal d).row) = _
  rw [D.map_add_univ]
  rw [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro I hI
  change det (Matrix.of (I.piecewise C.row (diagonal d).row)) = _
  rw [det_piecewise, ordered_minor]

#print axioms solution



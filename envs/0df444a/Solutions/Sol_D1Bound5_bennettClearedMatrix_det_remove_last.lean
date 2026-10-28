-- Prove2me | solution 1 for D1Bound5.bennettClearedMatrix_det_remove_last
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:37:53.78883+00:00
-- url     : https://prove2.me/submissions/5aa35b40-29b8-4446-a41d-6355215113fc

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettDeterminantConstant_Definitions
import Theorems.Thm_D1Bound5_bennettClearedResidue_diagonal_at_node
import Theorems.Thm_D1Bound5_bennettClearedResidue_offDiagonal_at_node
import Theorems.Thm_D1Bound5_bennettClearedResidue_prefix
import Theorems.Thm_D1Bound5_bennettClearedResidue_remove_node
import Theorems.Thm_D1Bound5_bennett_prod_erase_last

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]







/-- Exact determinant reduction at the removed node. Both directions of every
new node difference are retained, so this identity contains its full sign. -/
theorem _root_.solution
    (n : ℕ) (a : Fin (n + 1) → F) (ha : Function.Injective a)
    (k : ℕ) (hk : 1 ≤ k) (ν : F) :
    (bennettClearedMatrix a k ν).det.eval (-a (Fin.last n)) =
      Ring.choose ((k : F) + ν) k *
        (∏ j : Fin n, ((a (Fin.last n) - a j.castSucc)⁻¹) ^ k) *
        (∏ j : Fin n, ((a j.castSucc - a (Fin.last n))⁻¹) ^ k) *
        (bennettClearedMatrix (fun j : Fin n ↦ a j.castSucc) k
          (ν - (k : F))).det.eval (-a (Fin.last n)) := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    (bennettClearedMatrix a k ν).map (Polynomial.evalRingHom (-a (Fin.last n)))
  let B : Matrix (Fin n) (Fin n) F :=
    (bennettClearedMatrix (fun j : Fin n ↦ a j.castSucc) k (ν - (k : F))).map
      (Polynomial.evalRingHom (-a (Fin.last n)))
  have hsign : (-1 : F) ^ (n + n) = 1 := by
    calc
      _ = ((-1 : F) * (-1)) ^ n := by rw [pow_add, mul_pow]
      _ = _ := by simp
  have hdiag : A (Fin.last n) (Fin.last n) =
      Ring.choose ((k : F) + ν) k *
        ∏ j : Fin n, ((a (Fin.last n) - a j.castSucc)⁻¹) ^ k := by
    change (bennettClearedResidue Finset.univ a k ν (Fin.last n) (Fin.last n)).eval
      (-a (Fin.last n)) = _
    rw [bennettClearedResidue_diagonal_at_node, bennett_prod_erase_last]
  have hminor : A.submatrix Fin.castSucc Fin.castSucc =
      Matrix.of (fun i j : Fin n ↦ ((a j.castSucc - a (Fin.last n))⁻¹) ^ k * B i j) := by
    apply Matrix.ext
    intro i j
    change (bennettClearedResidue Finset.univ a k ν i.castSucc j.castSucc).eval
      (-a (Fin.last n)) =
        ((a j.castSucc - a (Fin.last n))⁻¹) ^ k *
          (bennettClearedResidue Finset.univ (fun l : Fin n ↦ a l.castSucc) k
            (ν - (k : F)) i j).eval (-a (Fin.last n))
    rw [bennettClearedResidue_remove_node Finset.univ a k ν i.castSucc j.castSucc
      (Fin.last n) (Finset.mem_univ _) (Fin.castSucc_ne_last i)
        (Fin.castSucc_ne_last j) (ha.ne (Fin.castSucc_ne_last j)),
      bennettClearedResidue_prefix]
  have hdet : A.det = A (Fin.last n) (Fin.last n) *
      (A.submatrix Fin.castSucc Fin.castSucc).det := by
    rw [Matrix.det_succ_column A (Fin.last n), Finset.sum_eq_single (Fin.last n)]
    · simp only [Fin.val_last, Fin.succAbove_last, hsign, one_mul]
    · intro i hi hne
      have hz : A i (Fin.last n) = 0 := by
        exact bennettClearedResidue_offDiagonal_at_node Finset.univ a k hk ν i
          (Fin.last n) hne
      rw [hz, mul_zero, zero_mul]
    · simp
  calc
    _ = A.det := (Polynomial.evalRingHom (-a (Fin.last n))).map_det _
    _ = _ := by
      rw [hdet, hdiag, hminor, Matrix.det_mul_row]
      have hB : B.det =
          (bennettClearedMatrix (fun j : Fin n ↦ a j.castSucc) k
            (ν - (k : F))).det.eval (-a (Fin.last n)) :=
        ((Polynomial.evalRingHom (-a (Fin.last n))).map_det _).symm
      rw [hB]
      ring

end D1Bound5
end

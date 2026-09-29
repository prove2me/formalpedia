-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.geometric_rank_one_determinant_affine
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T19:54:19.807392+00:00
-- url     : https://prove2.me/submissions/18535dff-1bfc-4e6e-ba49-7d20db57ef36

import Mathlib
open Matrix
namespace EulerHankel
lemma geometric_rank_one_affine {R : Type*} [CommRing R] (n : ℕ)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) (r : R) :
    ∃ a b : R, ∀ t : R,
      Matrix.det (fun i j => A i j + r^(i.val+j.val)*t) = a*t+b := by
  classical
  let N : Matrix (Fin (n+1)) (Fin (n+1)) R :=
    fun i j => if i=0 then A i j else A i j-r^i.val*A 0 j
  let v : Fin (n+1) → R := fun j => r^j.val
  refine ⟨(N.updateRow 0 v).det,N.det,?_⟩
  intro t
  let B : Matrix (Fin (n+1)) (Fin (n+1)) R := fun i j => A i j+r^(i.val+j.val)*t
  have hdet : (N.updateRow 0 (N 0+t • v)).det=B.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const
      (fun i : Fin (n+1) => if i=0 then 0 else -r^i.val) 0 (by simp)
    intro i j
    by_cases hi : i=0
    · subst i
      simp [N,B,v,Matrix.updateRow]
      ring
    · simp [N,B,v,Matrix.updateRow,hi,pow_add]
      ring
  change B.det = _
  rw [← hdet,Matrix.det_updateRow_add,Matrix.det_updateRow_smul,Matrix.updateRow_eq_self]
  ring
end EulerHankel


theorem solution {R : Type*} [CommRing R] (n : ℕ)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) (r : R) :
    ∃ a b : R, ∀ t : R,
      Matrix.det (fun i j => A i j + r^(i.val+j.val)*t) = a*t+b := by
  exact EulerHankel.geometric_rank_one_affine n A r
#print axioms solution

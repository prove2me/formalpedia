-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.blockExtend_mul_mul_eq_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:41.612177+00:00
-- url     : https://prove2.me/submissions/e9429d21-0dea-4e48-9a0c-46f2045e22b0

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_succ
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_zero_zero
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_zero_succ
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_succ_zero
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_succ_succ

set_option autoImplicit false
open Polynomial Matrix
open Formalism Formalism.CyclotomicNorms
noncomputable section
open Formalism.CyclotomicNorms.residueMatrixData
variable {R : Type*} [CommRing R]
namespace Formalism.CyclotomicNorms.residueMatrixData
theorem _root_.solution {a : ℕ} (P Q : Matrix (Fin a) (Fin a) R) (E : Matrix (Fin (a+1)) (Fin (a+1)) R)
    (h1 : ∀ j : Fin a, E 0 j.succ = 0) (h2 : ∀ i : Fin a, E i.succ 0 = 0) (d : Fin a → R)
    (hd : P * (Matrix.of fun i j : Fin a => E i.succ j.succ) * Q = diagonal d) :
    ext1 P * E * ext1 Q = diagonal (Fin.cons (E 0 0) d) := by
  ext i j
  have hd' : ∀ i j, (P * (Matrix.of fun i j : Fin a => E i.succ j.succ) * Q) i j = diagonal d i j := by
    rw [hd]; intros; rfl
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, h1, h2]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, h1, h2, diagonal_apply, (Fin.succ_ne_zero j).symm]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, h1, h2, diagonal_apply, (Fin.succ_ne_zero i)]
  · have := hd' i j
    simp only [Matrix.mul_apply, Matrix.of_apply] at this
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h1, h2, diagonal_apply]
    rw [this, diagonal_apply]
end Formalism.CyclotomicNorms.residueMatrixData

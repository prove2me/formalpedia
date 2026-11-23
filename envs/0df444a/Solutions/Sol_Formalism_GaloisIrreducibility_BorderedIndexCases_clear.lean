-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.BorderedIndexCases.clear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:07.845409+00:00
-- url     : https://prove2.me/submissions/d0911e16-b0af-4fe6-ad4d-b6c48e373bd6

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ'
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ

set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Matrix
open Matrix
open Formalism.GaloisIrreducibility.BorderedIndexCases
variable {R : Type} [CommRing R]
namespace Formalism.GaloisIrreducibility.BorderedIndexCases
theorem _root_.solution {m : ℕ} (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (hu : IsUnit (A 0 0)) :
    ∃ A' : Matrix (Fin m) (Fin m) R, Equi A (bord A') := by
  obtain ⟨b, hb⟩ : ∃ b : R, A 0 0 * b = 1 := ⟨_, hu.mul_val_inv⟩
  have hb' : b * A 0 0 = 1 := by rw [mul_comm]; exact hb
  set P : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons 1 0)
    (fun i => Fin.cons (-(A i.succ 0 * b)) (fun j => if i = j then 1 else 0))) with hP
  set Pinv : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons 1 0)
    (fun i => Fin.cons (A i.succ 0 * b) (fun j => if i = j then 1 else 0))) with hPinv
  set Q : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons b (fun j => -(b * A 0 j.succ)))
    (fun i => Fin.cons 0 (fun j => if i = j then 1 else 0))) with hQ
  set Qinv : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons (A 0 0) (fun j => A 0 j.succ))
    (fun i => Fin.cons 0 (fun j => if i = j then 1 else 0))) with hQinv
  set A' : Matrix (Fin m) (Fin m) R := Matrix.of fun i j => A i.succ j.succ - A i.succ 0 * b * A 0 j.succ
    with hA'
  have hPP : P * Pinv = 1 := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [hP, hPinv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  have hQQ : Q * Qinv = 1 := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [hQ, hQinv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, hb']
  have hPu : IsUnit P := by
    have h : P.det * Pinv.det = 1 := by rw [← Matrix.det_mul, hPP, Matrix.det_one]
    rw [Matrix.isUnit_iff_isUnit_det]
    first
    | exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
    | exact IsUnit.of_mul_eq_one _ h
  have hQu : IsUnit Q := by
    have h : Q.det * Qinv.det = 1 := by rw [← Matrix.det_mul, hQQ, Matrix.det_one]
    rw [Matrix.isUnit_iff_isUnit_det]
    first
    | exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
    | exact IsUnit.of_mul_eq_one _ h
  have key : P * A * Q = bord A' := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [hP, hQ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first | linear_combination hb | linear_combination (-1 : R) * hb
    · simp [hP, hQ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first | linear_combination (-(A 0 j.succ)) * hb | linear_combination (A 0 j.succ) * hb
    · simp [hP, hQ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first | linear_combination (-(A i.succ 0 * b)) * hb' | linear_combination (A i.succ 0 * b) * hb'
    · simp [hP, hQ, hA', Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first
        | linear_combination (A i.succ 0 * b * A 0 j.succ) * hb'
        | linear_combination (-(A i.succ 0 * b * A 0 j.succ)) * hb'
  refine ⟨A', ?_⟩
  unfold Equi
  exact ⟨P, Q, hPu, hQu, key⟩
end Formalism.GaloisIrreducibility.BorderedIndexCases

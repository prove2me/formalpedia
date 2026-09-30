-- Prove2me | solution 2 for BookProof.RitzPerturbation.rayleighVal_shiftOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T19:15:48.600752+00:00
-- url     : https://prove2.me/submissions/875a535b-ac3f-4467-92ed-b56d6ffdca6e

-- Generated from ChapterSirkRitzPerturbation.lean — solution of BookProof.RitzPerturbation.rayleighVal_shiftOp
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation









noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (T : F →L[ℂ] F) (c : ℝ) {x : F} (hx1 : ‖x‖ = 1) :
    rayleighVal (shiftOp T c) x = rayleighVal T x + c := by

  have hxx : (inner ℂ x x : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hx1]
    norm_num
  have happ : (shiftOp T c) x = T x + (c : ℂ) • x := by simp [shiftOp]
  rw [rayleighVal, happ, inner_add_right, inner_smul_right, hxx, mul_one, Complex.add_re]
  simp [rayleighVal]

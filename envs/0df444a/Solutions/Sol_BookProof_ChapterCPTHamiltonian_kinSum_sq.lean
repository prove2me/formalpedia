-- Prove2me | solution 1 for BookProof.ChapterCPTHamiltonian.kinSum_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:57:33.944255+00:00
-- url     : https://prove2.me/submissions/19726f6f-f010-4724-b3e1-5f5b6224abe9

-- Generated from ChapterCPTHamiltonian.lean — solution of BookProof.ChapterCPTHamiltonian.kinSum_sq
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
import Theorems.Thm_BookProof_ChapterCPTHamiltonian_Kin_anticomm
import Theorems.Thm_BookProof_ChapterCPTHamiltonian_Kin_sq
open BookProof.ChapterCPTHamiltonian



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (k : Fin 3 → ℝ) :
    (∑ j : Fin 3, (k j : ℂ) • Kin j) * (∑ j : Fin 3, (k j : ℂ) • Kin j)
      = (∑ j : Fin 3, (k j : ℂ) ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by

  simp only [Complex.coe_smul, Fin.sum_univ_three, Fin.isValue]
  simp only [Fin.isValue, mul_add, Algebra.mul_smul_comm, add_mul, Algebra.smul_mul_assoc, smul_add, sq]
  simp only [Fin.isValue, Kin_sq, ← smul_assoc, smul_eq_mul]
  have h_anticomm :
      Kin 1 * Kin 0 + Kin 0 * Kin 1 = 0 ∧ Kin 2 * Kin 0 + Kin 0 * Kin 2 = 0 ∧
        Kin 2 * Kin 1 + Kin 1 * Kin 2 = 0 :=
    ⟨Kin_anticomm 1 0 (by decide), Kin_anticomm 2 0 (by decide), Kin_anticomm 2 1 (by decide)⟩
  obtain ⟨h10, h20, h21⟩ := h_anticomm
  simp only [Fin.isValue, ← eq_sub_iff_add_eq', zero_sub, ← ext_iff,
    Matrix.smul_apply, Complex.real_smul, Complex.ofReal_mul, Matrix.sub_apply,
    smul_eq_mul, Matrix.add_apply] at h10 h20 h21 ⊢
  intro i j
  specialize h10 i j; specialize h20 i j; specialize h21 i j
  simp only [Matrix.one_apply] at ⊢
  rw [h10, h20, h21]
  simp only [Matrix.neg_apply]
  push_cast
  ring

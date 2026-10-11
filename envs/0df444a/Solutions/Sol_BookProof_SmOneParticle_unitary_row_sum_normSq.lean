-- Prove2me | solution 1 for BookProof.SmOneParticle.unitary_row_sum_normSq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:21:32.298301+00:00
-- url     : https://prove2.me/submissions/af1b7789-92ce-4520-8610-27ae95545194

-- Generated from ChapterSmOneParticle.lean — solution of BookProof.SmOneParticle.unitary_row_sum_normSq
import Mathlib
import Definitions.Def_ChapterSmOneParticle
open BookProof.SmOneParticle

variable {V U : Matrix (Fin 3) (Fin 3) ℂ}

set_option maxHeartbeats 1000000 in
theorem solution (hV : IsMixing V) (i : Fin 3) :
    ∑ j : Fin 3, ‖V i j‖ ^ 2 = 1 := by

  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i i) hV
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have hterm : ∀ j : Fin 3, V i j * star (V i j) = ((‖V i j‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [Finset.sum_congr rfl fun j _ => hterm j] at h
  exact_mod_cast h

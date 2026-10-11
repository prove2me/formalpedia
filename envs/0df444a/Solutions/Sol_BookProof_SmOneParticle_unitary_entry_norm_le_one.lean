-- Prove2me | solution 1 for BookProof.SmOneParticle.unitary_entry_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:14:45.902066+00:00
-- url     : https://prove2.me/submissions/082efc0c-884c-411c-9a98-fa927a0c5b52

-- Generated from ChapterSmOneParticle.lean — theorem BookProof.SmOneParticle.unitary_entry_norm_le_one
import Mathlib
import Definitions.Def_ChapterSmOneParticle
open BookProof.SmOneParticle

variable {V U : Matrix (Fin 3) (Fin 3) ℂ}
open BookProof.SmOneParticle

theorem solution(hV : IsMixing V) (i j : Fin 3) : ‖V i j‖ ≤ 1 := by
  unfold IsMixing at hV
  have h1 := congrFun (congrFun hV i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  simp only [Matrix.conjTranspose_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h1
  have h : ∑ k, ‖V i k‖ ^ 2 = 1 := by exact_mod_cast h1
  have h2 : ‖V i j‖ ^ 2 ≤ 1 := h ▸ Finset.single_le_sum (fun k _ => sq_nonneg ‖V i k‖) (Finset.mem_univ j)
  nlinarith [norm_nonneg (V i j)]

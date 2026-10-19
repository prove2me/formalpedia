-- Prove2me | solution 2 for BookProof.SmDiracYukawa.yukawa_entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:17:18.57981+00:00
-- url     : https://prove2.me/submissions/0bfbbc01-cb08-476c-ac58-b9bbb9de9ee6

import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterSmOneParticle
-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.yukawa_entry_bound
open BookProof.SmOneParticle
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

open BookProof.SmOneParticle
theorem h42_mix_mul {A B : Matrix (Fin 3) (Fin 3) ℂ} (hA : IsMixing A) (hB : IsMixing B) :
    IsMixing (A * B.conjTranspose) := by
  unfold IsMixing at *
  have hB' : B.conjTranspose * B = 1 := mul_eq_one_comm.1 hB
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc B.conjTranspose, hB', Matrix.one_mul, hA]

theorem h42_mix_entry {V : Matrix (Fin 3) (Fin 3) ℂ} (hV : IsMixing V) (i k : Fin 3) :
    ‖V i k‖ ≤ 1 := by
  have h := congrFun (congrFun hV i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have h2 : ∑ x, Complex.normSq (V i x) = 1 := by
    have := congrArg Complex.re h
    simpa [Complex.mul_conj] using this
  have h3 : Complex.normSq (V i k) ≤ 1 := by
    rw [← h2]
    exact Finset.single_le_sum (f := fun x => Complex.normSq (V i x))
      (fun x _ => Complex.normSq_nonneg _) (Finset.mem_univ k)
  have h4 : ‖V i k‖ ^ 2 ≤ 1 := by rw [Complex.sq_norm]; exact h3
  nlinarith [norm_nonneg (V i k)]

theorem h42_yuk {UL V UR D : Matrix (Fin 3) (Fin 3) ℂ}
    (hUL : IsMixing UL) (hV : IsMixing V) (hUR : IsMixing UR)
    (hD : ∀ k l, k ≠ l → D k l = 0) (i j : Fin 3) :
    ‖(UL * V.conjTranspose * D * UR.conjTranspose) i j‖ ≤ ∑ k : Fin 3, ‖D k k‖ := by
  have hW := h42_mix_mul hUL hV
  set W := UL * V.conjTranspose
  have e1 : ∀ k, (W * D) i k = W i k * D k k := by
    intro k
    rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · intro b _ hb; rw [hD b k hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [e1, Matrix.conjTranspose_apply, norm_mul, norm_mul, norm_star]
  have a := h42_mix_entry hW i k
  have b := h42_mix_entry hUR j k
  have := norm_nonneg (D k k)
  have := norm_nonneg (W i k)
  have := norm_nonneg (UR j k)
  nlinarith [mul_le_mul a b (norm_nonneg _) zero_le_one]

theorem solution {UL V UR D : Matrix (Fin 3) (Fin 3) ℂ}
    (hUL : IsMixing UL) (hV : IsMixing V) (hUR : IsMixing UR)
    (hD : ∀ k l, k ≠ l → D k l = 0) (i j : Fin 3) :
    ‖(UL * V.conjTranspose * D * UR.conjTranspose) i j‖ ≤ ∑ k : Fin 3, ‖D k k‖ := by
  exact h42_yuk hUL hV hUR hD i j


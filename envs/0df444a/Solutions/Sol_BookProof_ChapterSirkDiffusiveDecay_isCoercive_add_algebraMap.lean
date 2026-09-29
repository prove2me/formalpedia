-- Prove2me | solution 1 for BookProof.ChapterSirkDiffusiveDecay.isCoercive_add_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-09T12:13:17.774429+00:00
-- url     : https://prove2.me/submissions/6c021131-e4f7-4738-82f5-7da402b0bee9

-- Generated from ChapterSirkDiffusiveDecay.lean — solution of BookProof.ChapterSirkDiffusiveDecay.isCoercive_add_algebraMap
import Mathlib
import Definitions.Def_ChapterSirkDiffusiveDecay
open BookProof.ChapterSirkDiffusiveDecay










noncomputable section


open BookProof.ChapterH4
open Filter Topology NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (B : E →L[ℂ] E) (mu : ℝ)
    (hB : ∀ x : E, 0 ≤ (inner ℂ x (B x) : ℂ).re) :
    IsCoercive (B + (algebraMap ℝ (E →L[ℂ] E)) mu) mu := by

  intro x
  have h : (B + (algebraMap ℝ (E →L[ℂ] E)) mu) x = B x + (mu : ℂ) • x := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [h, inner_add_right, Complex.add_re, inner_smul_right]
  have hx : (((mu : ℂ) * (inner ℂ x x : ℂ))).re = mu * ‖x‖ ^ 2 := by
    simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  rw [hx]
  linarith [hB x]

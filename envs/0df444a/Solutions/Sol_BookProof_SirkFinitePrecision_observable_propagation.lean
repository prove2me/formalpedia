-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.observable_propagation
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:21:08.06513+00:00
-- url     : https://prove2.me/submissions/d8c94174-f43a-4e1a-aec7-1f8829ddae5b

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.observable_propagation
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision







noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (O : F →L[ℂ] F) (u w : F) :
    |(inner ℂ u (O u)).re - (inner ℂ w (O w)).re| ≤ ‖O‖ * (‖u‖ + ‖w‖) * ‖u - w‖ := by

  have hsplit : inner ℂ u (O u) - inner ℂ w (O w)
      = inner ℂ (u - w) (O u) + inner ℂ w (O (u - w)) := by
    have hO : O (u - w) = O u - O w := by simp
    rw [hO, inner_sub_left, inner_sub_right]
    ring
  have h1 : ‖inner ℂ (u - w) (O u)‖ ≤ ‖u - w‖ * (‖O‖ * ‖u‖) :=
    le_trans (norm_inner_le_norm _ _)
      (mul_le_mul_of_nonneg_left (O.le_opNorm u) (norm_nonneg _))
  have h2 : ‖inner ℂ w (O (u - w))‖ ≤ ‖w‖ * (‖O‖ * ‖u - w‖) :=
    le_trans (norm_inner_le_norm _ _)
      (mul_le_mul_of_nonneg_left (O.le_opNorm (u - w)) (norm_nonneg _))
  have hre : |(inner ℂ u (O u)).re - (inner ℂ w (O w)).re|
      ≤ ‖inner ℂ u (O u) - inner ℂ w (O w)‖ := by
    rw [← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  refine hre.trans ?_
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  nlinarith [h1, h2]

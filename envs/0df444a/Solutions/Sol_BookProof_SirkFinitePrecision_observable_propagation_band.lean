-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.observable_propagation_band
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:52:43.861367+00:00
-- url     : https://prove2.me/submissions/f02df20a-379f-4ad0-a5a5-1c7d0e61e35d

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.observable_propagation_band
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
import Theorems.Thm_BookProof_SirkFinitePrecision_observable_propagation
open BookProof.SirkFinitePrecision







noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (O : F →L[ℂ] F) (u w : F) {R band : ℝ}
    (hu : ‖u‖ ≤ R) (hw : ‖w‖ ≤ R) (hband : ‖u - w‖ ≤ band) :
    |(inner ℂ u (O u)).re - (inner ℂ w (O w)).re| ≤ 2 * ‖O‖ * R * band := by

  refine (observable_propagation O u w).trans ?_
  have hO : (0 : ℝ) ≤ ‖O‖ := norm_nonneg _
  have hR : (0 : ℝ) ≤ R := le_trans (norm_nonneg u) hu
  have hb : (0 : ℝ) ≤ ‖u - w‖ := norm_nonneg _
  have h1 : ‖u‖ + ‖w‖ ≤ 2 * R := by linarith
  calc ‖O‖ * (‖u‖ + ‖w‖) * ‖u - w‖ ≤ ‖O‖ * (2 * R) * ‖u - w‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hO) hb
    _ ≤ ‖O‖ * (2 * R) * band := mul_le_mul_of_nonneg_left hband (by positivity)
    _ = 2 * ‖O‖ * R * band := by ring

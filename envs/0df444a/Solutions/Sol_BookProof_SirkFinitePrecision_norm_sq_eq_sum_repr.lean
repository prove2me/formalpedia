-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.norm_sq_eq_sum_repr
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:19:25.828828+00:00
-- url     : https://prove2.me/submissions/07ebb2d4-f778-4cd5-8b5a-6882b5c78830

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.norm_sq_eq_sum_repr
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision







noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ‖coeff hT hn x i‖ ^ 2 := by

  rw [← (hT.eigenvectorBasis hn).repr.norm_map x]
  exact EuclideanSpace.norm_sq_eq _

-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.index_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:51:12.443582+00:00
-- url     : https://prove2.me/submissions/f8001db0-08a3-4a1e-a1f8-8d3daefee9ab

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.index_nonempty
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
import Theorems.Thm_BookProof_SirkFinitePrecision_norm_sq_eq_sum_repr
open BookProof.SirkFinitePrecision







noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {x : E} (hx : x ≠ 0) :
    (univ : Finset (Fin n)).Nonempty := by

  rcases Finset.eq_empty_or_nonempty (univ : Finset (Fin n)) with h | h
  · exfalso
    apply hx
    have hsum := norm_sq_eq_sum_repr hT hn x
    rw [h, Finset.sum_empty] at hsum
    have : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp this
  · exact h

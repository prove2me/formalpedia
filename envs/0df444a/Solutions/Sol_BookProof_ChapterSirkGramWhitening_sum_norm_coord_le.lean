-- Prove2me | solution 1 for BookProof.ChapterSirkGramWhitening.sum_norm_coord_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:40:19.7421+00:00
-- url     : https://prove2.me/submissions/8ba2848b-ad32-48d0-9d6b-6d061ff11bc0

-- Generated from ChapterSirkGramWhitening.lean — solution of BookProof.ChapterSirkGramWhitening.sum_norm_coord_le
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening









noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} (c : EuclideanSpace ℂ (Fin m)) :
    ∑ i, ‖c i‖ ≤ Real.sqrt m * ‖c‖ := by

  have h1 : (∑ i, ‖c i‖) ^ 2 ≤ (m : ℝ) * ∑ i, ‖c i‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => ‖c i‖)
  have h2 : ‖c‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  have h3 : (0 : ℝ) ≤ ∑ i, ‖c i‖ := by positivity
  have h4 : (∑ i, ‖c i‖) ^ 2 ≤ (Real.sqrt m * ‖c‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ)), h2]
    exact h1
  have h5 : (0 : ℝ) ≤ Real.sqrt m * ‖c‖ := by positivity
  nlinarith [h4, h3, h5]

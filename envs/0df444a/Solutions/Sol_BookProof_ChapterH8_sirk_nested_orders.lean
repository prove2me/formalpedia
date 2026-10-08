-- Prove2me | solution 1 for BookProof.ChapterH8.sirk_nested_orders
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:48:42.019807+00:00
-- url     : https://prove2.me/submissions/58c2ba6d-444d-49c1-be84-a2e0eebfb484

-- Generated from ChapterH8.lean — solution of BookProof.ChapterH8.sirk_nested_orders
import Mathlib
import Definitions.Def_ChapterH8
import Theorems.Thm_BookProof_ChapterH8_sirk_krylov_tower
import Theorems.Thm_BookProof_ChapterH8_sirk_band_contained
open BookProof.ChapterH8



noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (H : E →ₗ[K] E) (v : E) (C Dmin h nv : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ Dmin) (hnv : 0 ≤ nv) (hh : 0 ≤ h) :
    ∀ n : ℕ, krylovSpan H v n ≤ krylovSpan H v (n + 1)
      ∧ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv (n + 1))
          ⊆ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv n) := fun n => ⟨sirk_krylov_tower H v n, sirk_band_contained C Dmin h nv hC hD hnv hh n⟩

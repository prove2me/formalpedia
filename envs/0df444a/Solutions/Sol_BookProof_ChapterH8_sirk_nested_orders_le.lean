-- Prove2me | solution 1 for BookProof.ChapterH8.sirk_nested_orders_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:52:16.697211+00:00
-- url     : https://prove2.me/submissions/01743197-51f1-4ef2-9a9d-0a638cc45490

-- Generated from ChapterH8.lean — solution of BookProof.ChapterH8.sirk_nested_orders_le
import Mathlib
import Definitions.Def_ChapterH8
import Theorems.Thm_BookProof_ChapterH8_sirk_band_contained_le
import Theorems.Thm_BookProof_ChapterH5_krylovSpan_mono
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
    (hC : 0 ≤ C) (hD : 0 ≤ Dmin) (hnv : 0 ≤ nv) (hh : 0 ≤ h) {m n : ℕ} (hmn : m ≤ n) :
    krylovSpan H v m ≤ krylovSpan H v n
      ∧ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv n)
          ⊆ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv m) := ⟨krylovSpan_mono hmn, sirk_band_contained_le C Dmin h nv hC hD hnv hh hmn⟩

-- Prove2me | solution 1 for BookProof.ChapterA.qembed_injective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:46:11.227739+00:00
-- url     : https://prove2.me/submissions/f303c42f-2ed0-4ae0-8d9c-af4cda59551a

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.qembed_injective
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial V] (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = -x) :
    Function.Injective (qembed θ hθ) := by

  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h
  have h1 : (qembed θ hθ) (a⁻¹ * a) = 1 := by
    rw [inv_mul_cancel₀ h]; exact map_one _
  rw [map_mul, ha, mul_zero] at h1
  exact one_ne_zero h1.symm

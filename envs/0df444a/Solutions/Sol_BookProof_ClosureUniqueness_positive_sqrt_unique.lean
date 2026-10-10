-- Prove2me | solution 1 for BookProof.ClosureUniqueness.positive_sqrt_unique
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:19:50.477188+00:00
-- url     : https://prove2.me/submissions/360e2493-9f0c-494c-a3d8-629689246655

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.positive_sqrt_unique
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Theorems.Thm_BookProof_ClosureUniqueness_positive_factor_unique
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}
variable [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S B C : H →L[ℂ] H) (hB : B.IsPositive) (hC : C.IsPositive)
    (hBS : B ∘L B = S) (hCS : C ∘L C = S) : B = C := positive_factor_unique B C hB hC (by rw [hBS, hCS])

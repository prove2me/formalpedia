-- Prove2me | solution 1 for BookProof.ChapterA.commuting_antiUnitary_scalar_multiple
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:43:48.438921+00:00
-- url     : https://prove2.me/submissions/b477522c-f7a8-49df-b4ce-d22dd6ce7781

-- Generated from ChapterA2.lean — solution of BookProof.ChapterA.commuting_antiUnitary_scalar_multiple
import Mathlib
import Definitions.Def_ChapterA2
import Theorems.Thm_BookProof_ChapterA_antiisometry_unique_up_to_phase
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) (hSchur : IsSchurUnitary M)
    {θ₁ θ₂ : AntiUnitary V} (h₁ : CommutesAntiUnitary M θ₁) (h₂ : CommutesAntiUnitary M θ₂) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, θ₂ x = c • θ₁ x := antiisometry_unique_up_to_phase M hSchur h₁ h₂

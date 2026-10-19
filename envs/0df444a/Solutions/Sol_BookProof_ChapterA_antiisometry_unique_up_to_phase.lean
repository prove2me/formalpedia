-- Prove2me | solution 1 for BookProof.ChapterA.antiisometry_unique_up_to_phase
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:43:47.3802+00:00
-- url     : https://prove2.me/submissions/87841858-a767-435b-8589-5ed0042ebf5d

-- Generated from ChapterA2.lean — solution of BookProof.ChapterA.antiisometry_unique_up_to_phase
import Mathlib
import Definitions.Def_ChapterA2
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) (hSchur : IsSchurUnitary M)
    {θ₁ θ₂ : AntiUnitary V} (h₁ : CommutesAntiUnitary M θ₁) (h₂ : CommutesAntiUnitary M θ₂) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, θ₂ x = c • θ₁ x := by

  -- `θ₁⁻¹` commutes with `M`.
  have h₁' : ∀ m ∈ M.ops, ∀ x, θ₁.symm (m x) = m (θ₁.symm x) := by
    intro m hm x
    apply θ₁.injective
    rw [θ₁.apply_symm_apply, h₁ m hm, θ₁.apply_symm_apply]
  -- `g := θ₂ ∘ θ₁⁻¹` is a `ℂ`-linear isometry commuting with `M`.
  set g : V ≃ₗᵢ[ℂ] V := θ₁.symm.trans θ₂ with hg
  have hgapp : ∀ x, g x = θ₂ (θ₁.symm x) := fun x => rfl
  have hgcomm : CommutesUnitary M g := by
    intro m hm x
    rw [hgapp, hgapp, h₁' m hm, h₂ m hm]
  obtain ⟨c, hc, hcg⟩ := hSchur g hgcomm
  refine ⟨c, hc, fun x => ?_⟩
  have := hcg (θ₁ x)
  rwa [hgapp, θ₁.symm_apply_apply] at this

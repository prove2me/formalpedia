-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.rangeA_excZeros_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:34:58.809703+00:00
-- url     : https://prove2.me/submissions/4ef96c16-2494-41d9-aa6c-1c23645ff4f5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTRangeA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_eOf_exc
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_zero_in_region


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M) (β : ℝ)
    (h : eOf M = some (χ, β)) (hr : InRegion cZ M (β : ℂ)) : ExcZeros cZ χ {β} := by
  have he := eOf_exc M _ h
  have hz : IsLZero χ (β : ℂ) := ⟨Or.inl he.2.1, he.2.2.1⟩
  obtain ⟨-, -, -, hd⟩ := zero_in_region M hM χ _ hr hz
  refine ⟨by simp, ?_, ?_⟩
  · intro b hb
    rw [Finset.mem_singleton] at hb
    subst hb
    exact ⟨he.2.1, hr, he.2.2.1, hd⟩
  · intro s hs hz'
    obtain ⟨β₁, h1, h2, -⟩ := zero_in_region M hM χ s hs hz'
    rw [h] at h1
    have : β = β₁ := by simpa using h1
    exact ⟨β, by simp, by rw [h2, this]⟩
end Formalism.HermitianLattices.Ext.PrimesInProgressions

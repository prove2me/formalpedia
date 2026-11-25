-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.rangeA_excZeros_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:34:55.784457+00:00
-- url     : https://prove2.me/submissions/fa639b6f-b6e7-44ad-9411-618ce3985810

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTRangeA
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
theorem _root_.solution (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M)
    (h : ∀ β : ℝ, eOf M = some (χ, β) → ¬ InRegion cZ M (β : ℂ)) : ExcZeros cZ χ ∅ := by
  refine ⟨by simp, by simp, ?_⟩
  intro s hs hz
  obtain ⟨β₁, h1, h2, -⟩ := zero_in_region M hM χ s hs hz
  exact absurd (h2 ▸ hs) (h β₁ h1)
end Formalism.HermitianLattices.Ext.PrimesInProgressions

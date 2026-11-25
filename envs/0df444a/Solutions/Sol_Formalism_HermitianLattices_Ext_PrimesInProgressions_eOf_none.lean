-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.eOf_none
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:54:37.495156+00:00
-- url     : https://prove2.me/submissions/2d7c05aa-6dbe-4143-aded-73cb94d0d012

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_eOf_cases

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
theorem _root_.solution (M : ℕ) [NeZero M] (h : eOf M = none) (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ) :
    ¬ IsExcPair χ₁ β₁ := by
  rcases eOf_cases M with ⟨q, hq, _, _⟩ | ⟨q, hq, _, _⟩ | ⟨_, hno⟩
  · rw [h] at hq
    cases hq
  · rw [h] at hq
    cases hq
  · exact hno (χ₁, β₁)
end Formalism.HermitianLattices.Ext.PrimesInProgressions

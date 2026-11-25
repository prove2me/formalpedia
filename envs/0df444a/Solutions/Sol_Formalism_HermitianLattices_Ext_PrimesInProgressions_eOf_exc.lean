-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.eOf_exc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:11:20.189353+00:00
-- url     : https://prove2.me/submissions/ef27ace0-9724-43f0-a555-8bfdc9b75ab7

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
theorem _root_.solution (M : ℕ) [NeZero M] (p : DirichletCharacter ℂ M × ℝ) (h : eOf M = some p) :
    IsExcPair p.1 p.2 := by
  rcases eOf_cases M with ⟨q, hq, hex, _⟩ | ⟨q, hq, hex, _⟩ | ⟨hn, _⟩
  · rw [h] at hq
    cases hq
    exact hex
  · rw [h] at hq
    cases hq
    exact hex
  · rw [h] at hn
    cases hn
end Formalism.HermitianLattices.Ext.PrimesInProgressions

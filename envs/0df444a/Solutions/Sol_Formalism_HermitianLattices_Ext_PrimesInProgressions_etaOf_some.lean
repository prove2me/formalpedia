-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.etaOf_some
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:57:18.255037+00:00
-- url     : https://prove2.me/submissions/8f5fa72c-9581-41b9-b255-1a92fcd9423c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf

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
theorem _root_.solution (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ) (h : eOf M = some (χ₁, β₁)) :
    etaOf M = min 1 ((1 - β₁) * Real.log M) := by
  unfold etaOf
  rw [h]
end Formalism.HermitianLattices.Ext.PrimesInProgressions

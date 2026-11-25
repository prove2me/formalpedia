-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_one_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:13:08.444923+00:00
-- url     : https://prove2.me/submissions/ed47d8ba-28aa-4561-bfbe-e73ec63919d0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
variable {M : ℕ} [NeZero M]
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution : exLF (1 : DirichletCharacter ℂ M) = DirichletCharacter.LFunctionTrivChar₁ M := by
  unfold exLF; rw [if_pos rfl]
end Formalism.HermitianLattices.Ext.PrimesInProgressions

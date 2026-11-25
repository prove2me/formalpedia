-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.log_pos_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:56:12.591796+00:00
-- url     : https://prove2.me/submissions/ccf54195-c2f0-4553-8d15-142a12127b31

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
theorem _root_.solution (M : ℕ) (hM : 2 ≤ M) : 0 < Real.log M := by
  apply Real.log_pos
  exact_mod_cast (show 1 < M by omega)
end Formalism.HermitianLattices.Ext.PrimesInProgressions

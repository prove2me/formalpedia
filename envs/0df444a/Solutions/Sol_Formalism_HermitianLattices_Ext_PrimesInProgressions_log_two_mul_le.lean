-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.log_two_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:53:00.667409+00:00
-- url     : https://prove2.me/submissions/b678be69-57f4-4c87-8864-d4ac8ea2c776

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
theorem _root_.solution (M : ℕ) (hM : 2 ≤ M) : Real.log ((M : ℝ) * 2) ≤ 2 * Real.log M := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  rw [Real.log_mul (by positivity) (by norm_num)]
  have h1 : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hM'
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions

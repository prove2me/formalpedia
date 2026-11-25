-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.logMT_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:33:06.594478+00:00
-- url     : https://prove2.me/submissions/8c478986-a188-49f0-ae8b-b39fcdadf19e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinish

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
open Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
theorem _root_.solution (M : ℕ) (T : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) : 1 ≤ Real.log ((M : ℝ) * T) := by
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx : (6 : ℝ) ≤ M * T := by nlinarith
  have he := Real.exp_one_lt_d9
  have h1 : Real.exp 1 ≤ (M : ℝ) * T := by linarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log ((M : ℝ) * T) := Real.log_le_log (Real.exp_pos 1) h1
end Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF

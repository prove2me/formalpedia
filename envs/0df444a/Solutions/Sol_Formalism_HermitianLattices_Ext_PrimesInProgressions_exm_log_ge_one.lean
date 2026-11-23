-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_log_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:21.264753+00:00
-- url     : https://prove2.me/submissions/286c399f-67fa-41e2-a4bd-0a4fa70505ee

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplMainA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (M T : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) : 1 ≤ Real.log (M * T) := by
  have h6 : 6 ≤ M * T := by nlinarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (M * T) := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
end Formalism.HermitianLattices.Ext.PrimesInProgressions

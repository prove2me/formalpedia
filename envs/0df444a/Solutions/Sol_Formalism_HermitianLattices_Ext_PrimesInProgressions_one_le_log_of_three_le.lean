-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.one_le_log_of_three_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:31.156271+00:00
-- url     : https://prove2.me/submissions/2c3d4c18-2d64-4257-bcf9-fe336423cd65

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTBAsmA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  have h3 : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) h3
end Formalism.HermitianLattices.Ext.PrimesInProgressions

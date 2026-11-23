-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_log_y
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:38.020959+00:00
-- url     : https://prove2.me/submissions/09b5222d-ad98-415e-a40f-ef137e96e8ca

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
theorem _root_.solution (y : ℝ) (hy : 2 ≤ y) : 1 / 2 ≤ Real.log y := by
  calc (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    _ ≤ Real.log y := Real.log_le_log (by norm_num) hy
end Formalism.HermitianLattices.Ext.PrimesInProgressions

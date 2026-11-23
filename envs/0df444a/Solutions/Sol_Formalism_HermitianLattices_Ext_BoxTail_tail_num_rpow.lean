-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tail_num_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:12.350691+00:00
-- url     : https://prove2.me/submissions/dd00b3d7-e4a4-4de1-94c2-1be39222b12b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailNum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution (x ε : ℝ) (hx : 0 < x) :
    (x ^ 400) ^ (1 - 1 / 400 + ε / 1600 : ℝ) = x ^ 399 * x ^ (ε / 4) := by
  rw [← Real.rpow_natCast x 400, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x 399,
    ← Real.rpow_add hx]
  congr 1
  push_cast
  ring
end Formalism.HermitianLattices.Ext.BoxTail

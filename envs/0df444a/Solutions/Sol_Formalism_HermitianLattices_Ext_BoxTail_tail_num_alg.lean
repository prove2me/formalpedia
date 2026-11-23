-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tail_num_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:02.143978+00:00
-- url     : https://prove2.me/submissions/7fe7e228-9276-4411-8387-8e42a97f2f43

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
theorem _root_.solution (x Q K l a g : ℝ) (hx : 0 < x) (hQ : 0 < Q) :
    x * ((K * l * (l * (1 / x ^ 2) * (x ^ 399 * a) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * g / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2)))
      = K * l ^ 2 * a + K * (l * x ^ 403 / Q) + (x ^ 398 + 1) * g / x ^ 399 := by
  have hx0 : x ≠ 0 := hx.ne'
  have hQ0 : Q ≠ 0 := hQ.ne'
  field_simp
end Formalism.HermitianLattices.Ext.BoxTail

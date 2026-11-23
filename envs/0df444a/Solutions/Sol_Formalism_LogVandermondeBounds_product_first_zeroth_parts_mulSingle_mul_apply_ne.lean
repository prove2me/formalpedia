-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.mulSingle_mul_apply_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:34.9872+00:00
-- url     : https://prove2.me/submissions/61c5a551-49f7-4517-a332-5f6bba3bd5bd

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_MulSingleMulApplySelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
variable {ι H K : Type} [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [DecidableEq H] [Field K]
omit [Fintype H]
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution (v w : ι) (c : H) (h : ι → H) (hw : w ≠ v) :
    ((Pi.mulSingle v c : ι → H) * h) w = h w := by
  rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hw, _root_.one_mul]
end Formalism.LogVandermondeBounds.product_first_zeroth_parts

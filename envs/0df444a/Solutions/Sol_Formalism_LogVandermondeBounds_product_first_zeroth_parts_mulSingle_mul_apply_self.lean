-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.mulSingle_mul_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:35.016201+00:00
-- url     : https://prove2.me/submissions/8c2499fa-fc0d-4d4e-91be-061a0287382c

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
theorem _root_.solution (v : ι) (c : H) (h : ι → H) :
    ((Pi.mulSingle v c : ι → H) * h) v = c * h v := by
  rw [Pi.mul_apply, Pi.mulSingle_eq_same]
end Formalism.LogVandermondeBounds.product_first_zeroth_parts

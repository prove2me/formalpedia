-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.up_down_operators_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:38:59.7158+00:00
-- url     : https://prove2.me/submissions/ba341f36-548b-4364-831f-af839535d78f

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity

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
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution : AdjointReformulated := by
  intro k _ _ _ r R _ ψ φ
  unfold opU opD
  simp only [Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun f _ => ?_))
  split_ifs <;> ring
end Formalism.LogVandermondeBounds.product_first_zeroth_parts

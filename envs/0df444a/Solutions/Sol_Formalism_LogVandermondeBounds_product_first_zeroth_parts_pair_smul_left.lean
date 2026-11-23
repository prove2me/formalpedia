-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.pair_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:35.053216+00:00
-- url     : https://prove2.me/submissions/06c1ced5-eb16-4951-a812-5aa7b2c60ac7

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
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution (c : k) (f x : Fin r → k) : pair (c • f) x = c * pair f x := by
  unfold pair; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by simp [mul_assoc])
end Formalism.LogVandermondeBounds.product_first_zeroth_parts

-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.pair_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:47.28403+00:00
-- url     : https://prove2.me/submissions/a011cf5b-e1ec-40b0-97b9-a3b2ec8478e1

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_pair_comm
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_pair_smul_left

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
theorem _root_.solution (c : k) (f x : Fin r → k) : pair f (c • x) = c * pair f x := by
  rw [pair_comm, pair_smul_left, pair_comm]
end Formalism.LogVandermondeBounds.product_first_zeroth_parts

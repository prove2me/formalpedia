-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.ne_zero_of_pair_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:59:10.313016+00:00
-- url     : https://prove2.me/submissions/e7d8bba0-2619-4742-aca8-d322469bb847

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_pair_zero_right

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
theorem _root_.solution {f x : Fin r → k} (h : pair f x = 1) : x ≠ 0 := by
  rintro rfl; rw [pair_zero_right] at h; exact zero_ne_one h
end Formalism.LogVandermondeBounds.product_first_zeroth_parts

-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.factor_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:36:44.562973+00:00
-- url     : https://prove2.me/submissions/49e7b82d-6269-4b96-8087-271f7acb8a08

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution (q : ℝ) (hq : q ≠ 0) (n i : ℕ) (hi : i ≤ n) :
    q ^ n - q ^ i = q ^ n * (1 - q⁻¹ ^ (n - i)) := by
  have h : q ^ n * q⁻¹ ^ (n - i) = q ^ i := by
    rw [inv_pow, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ hq), ← pow_add, Nat.add_sub_of_le hi]
  rw [mul_sub, mul_one, h]
end Formalism.LogVandermondeBounds.StandardLattice

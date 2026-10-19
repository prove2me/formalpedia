-- Prove2me | solution 1 for CohnElkies.oddDoubleFactorial_mul_two_pow_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/a56289ea-c940-4cf1-9d50-b0c63265ddb7

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology
namespace CohnElkies
theorem _root_.solution (k : ℕ) :
    ((2 * k + 1)‼ : ℝ) * (2 : ℝ) ^ k * (k.factorial : ℝ) =
      ((2 * k + 1).factorial : ℝ) := by
  exact_mod_cast
    (by
      rw [mul_assoc, ← Nat.doubleFactorial_two_mul,
        ← Nat.factorial_eq_mul_doubleFactorial]
      : (2 * k + 1)‼ * 2 ^ k * k.factorial =
          (2 * k + 1).factorial)
end CohnElkies

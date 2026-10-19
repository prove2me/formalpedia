-- Prove2me | solution 1 for CohnElkies.unitBallVolume_odd_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/a90c39c2-9127-4255-8955-c5d6eb4d48e8

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_unitBallVolume_odd
import Theorems.Thm_CohnElkies_oddDoubleFactorial_mul_two_pow_factorial

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
    unitBallVolume (2 * k + 1) =
      Real.pi ^ k * (2 : ℝ) ^ (2 * k + 1) * (k.factorial : ℝ) /
        ((2 * k + 1).factorial : ℝ) := by
  rw [unitBallVolume_odd]
  have hdouble : ((2 * k + 1)‼ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.doubleFactorial_pos (2 * k + 1)))
  have hfactorial : ((2 * k + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.factorial_pos (2 * k + 1)))
  have hidentity := oddDoubleFactorial_mul_two_pow_factorial k
  have hpower :
      (2 : ℝ) ^ (2 * k + 1) =
        (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ k := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpower]
  field_simp
  nlinarith [hidentity]
end CohnElkies

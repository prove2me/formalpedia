-- Prove2me | solution 1 for CohnElkies.manuscriptLinearProgram_eq_binary_error_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/0aab104f-2c92-4e54-9637-6bb21e7abc94

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (hpositive : 0 < linearProgram d) :
    linearProgram d =
      (2 : ℝ) ^
        (-(criticalBinaryExponent + manuscriptBinaryExponentError d) *
          (d : ℝ)) := by
  have hdreal : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  have hexponent :
      -(criticalBinaryExponent + manuscriptBinaryExponentError d) *
        (d : ℝ) = Real.logb 2 (linearProgram d) := by
    unfold manuscriptBinaryExponentError
    field_simp
    ring
  rw [hexponent]
  exact (Real.rpow_logb (by norm_num) (by norm_num) hpositive).symm
end CohnElkies

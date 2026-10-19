-- Prove2me | solution 2 for CohnElkies.manuscriptLinearProgram_eq_binary_error_rpow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:13.663282+00:00
-- url     : https://prove2.me/submissions/ee6704b4-a6e9-40dd-b20b-38f3c7b4d3ff

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


theorem solution
    {d : ℕ} (hd : 0 < d) (hpositive : 0 < linearProgram d) :
    linearProgram d =
      (2 : ℝ) ^
        (-(criticalBinaryExponent + manuscriptBinaryExponentError d) *
          (d : ℝ)) := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  have : -(criticalBinaryExponent + manuscriptBinaryExponentError d) * (d : ℝ) =
      Real.logb 2 (linearProgram d) := by
    unfold manuscriptBinaryExponentError; field_simp; ring
  rw [this, Real.rpow_logb (by norm_num) (by norm_num) hpositive]


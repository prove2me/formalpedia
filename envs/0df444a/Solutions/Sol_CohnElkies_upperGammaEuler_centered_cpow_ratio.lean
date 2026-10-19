-- Prove2me | solution 1 for CohnElkies.upperGammaEuler_centered_cpow_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/c1e8d793-aff0-4e6d-9a30-a049d9bf2fe9

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    (m b : ℝ) {n : ℕ} (hn : 0 < n) :
    (n : ℂ) ^ ((m : ℂ) - Complex.I * (b : ℂ)) /
        (n : ℂ) ^ (m : ℂ) =
      Complex.exp
        (-Complex.I * ((b * Real.log (n : ℝ) : ℝ) : ℂ)) := by
  have hncomplex : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hncomplex,
    Complex.cpow_def_of_ne_zero hncomplex,
    ← Complex.exp_sub]
  rw [← Complex.natCast_log]
  congr 1
  push_cast
  ring
end CohnElkies

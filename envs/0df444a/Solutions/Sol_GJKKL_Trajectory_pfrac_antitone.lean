-- Prove2me | solution 1 for GJKKL.Trajectory.pfrac_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:27:20.226265+00:00
-- url     : https://prove2.me/submissions/ebed33b1-fb0c-4d12-9aca-22ff9ebd0fd5

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Functions

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory
open Finset
namespace GJKKL.Trajectory
theorem _root_.solution {a : ℝ} (ha : 0 ≤ a) {s t : ℕ} (hst : s ≤ t) :
    pfrac a t ≤ pfrac a s := by
  unfold pfrac
  have : (s : ℝ) / a ≤ t / a := div_le_div_of_nonneg_right (by exact_mod_cast hst) ha
  linarith
end GJKKL.Trajectory

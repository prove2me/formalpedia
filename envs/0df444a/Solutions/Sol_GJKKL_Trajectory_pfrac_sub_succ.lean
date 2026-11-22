-- Prove2me | solution 1 for GJKKL.Trajectory.pfrac_sub_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:35.918584+00:00
-- url     : https://prove2.me/submissions/7432c994-74d1-4bcc-96db-138938fa7963

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Functions

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory
open Finset
namespace GJKKL.Trajectory
theorem _root_.solution (a : ℝ) (t : ℕ) : pfrac a t - pfrac a (t + 1) = 1 / a := by
  unfold pfrac; push_cast; ring
end GJKKL.Trajectory

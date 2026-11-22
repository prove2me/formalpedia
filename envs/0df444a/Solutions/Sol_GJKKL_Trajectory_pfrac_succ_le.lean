-- Prove2me | solution 1 for GJKKL.Trajectory.pfrac_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:38:51.084631+00:00
-- url     : https://prove2.me/submissions/9dbf8b34-6bf2-4997-b2d1-fd841d1aa1a2

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Theorems.Thm_GJKKL_Trajectory_pfrac_sub_succ

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory
open Finset
namespace GJKKL.Trajectory
theorem _root_.solution (a : ℝ) (ha : 0 ≤ a) (t : ℕ) : pfrac a (t + 1) ≤ pfrac a t := by
  have := pfrac_sub_succ a t
  have : 0 ≤ 1 / a := by positivity
  linarith
end GJKKL.Trajectory

-- Prove2me | solution 1 for GJKKL.Trajectory.pfrac_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:56.808901+00:00
-- url     : https://prove2.me/submissions/dea0ebe6-a7b8-4e73-ab86-34016d0f6233

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Functions

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory
open Finset
namespace GJKKL.Trajectory
theorem _root_.solution {a : ℝ} (ha : 0 ≤ a) (t : ℕ) : pfrac a t ≤ 1 := by
  unfold pfrac
  have : 0 ≤ (t : ℝ) / a := div_nonneg (Nat.cast_nonneg t) ha
  linarith
end GJKKL.Trajectory

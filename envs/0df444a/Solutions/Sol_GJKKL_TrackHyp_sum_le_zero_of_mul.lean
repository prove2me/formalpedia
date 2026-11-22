-- Prove2me | solution 1 for GJKKL.TrackHyp.sum_le_zero_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:54.201964+00:00
-- url     : https://prove2.me/submissions/3fb96d06-67ac-4bf9-91cd-11d7c1f4fc7d

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
open GJKKL.TrackHyp
variable {H : Finset (Finset V)} {k c : ℕ} {dh δ : ℕ → ℝ} {T : ℕ} {B lam C s : ℝ}
  (hyp : TrackHyp H k c dh δ T B lam C s)
include hyp
namespace GJKKL.TrackHyp
theorem _root_.solution {S A : ℝ} (hA : 0 < A) (h : A * S ≤ 0) : S ≤ 0 := by
  by_contra hS
  push_neg at hS
  exact absurd h (not_le.mpr (mul_pos hA hS))
end GJKKL.TrackHyp

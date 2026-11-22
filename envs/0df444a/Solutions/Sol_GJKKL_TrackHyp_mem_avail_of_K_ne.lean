-- Prove2me | solution 1 for GJKKL.TrackHyp.mem_avail_of_K_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:53:09.494646+00:00
-- url     : https://prove2.me/submissions/8eb6ca06-949b-4cc3-8d22-33ef8607ea2d

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Theorems.Thm_GJKKL_greedyKernel_K_pos_iff


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
theorem _root_.solution {h : List (Finset V)} {a : Finset V}
    (ha : (greedyKernel H).K h a ≠ 0) : a ∈ avail H h :=
  greedyKernel_K_pos_iff.mp (lt_of_le_of_ne ((greedyKernel H).nonneg h a) (Ne.symm ha))
end GJKKL.TrackHyp

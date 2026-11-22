-- Prove2me | solution 1 for GJKKL.TrackHyp.aliveBefore_good_manyAvail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:54.294597+00:00
-- url     : https://prove2.me/submissions/8c9f15ee-4f68-435d-9cc6-d69e39d5ad52

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Theorems.Thm_GJKKL_TrackHyp_avail_bounds

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
theorem _root_.solution :
    ∀ h : List (Finset V), AliveBefore (GoodState H dh δ) h →
      ManyAvail H (fun t => aPar V k t * (dh t - δ t)) h
  | [], _ => trivial
  | a :: h, hal => ⟨solution h hal.1,
      (hyp.avail_bounds hal.2.1 hal.2.2.1).1⟩
end GJKKL.TrackHyp

-- Prove2me | solution 1 for GJKKL.TrackHyp.dv_le_card_avail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:25.668468+00:00
-- url     : https://prove2.me/submissions/497137ae-78ba-4ce7-a297-ab8f72ee560e

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
theorem _root_.solution (h : List (Finset V)) (v : V) :
    (dv H h v : ℝ) ≤ (avail H h).card := by
  exact_mod_cast card_le_card (filter_subset _ (avail H h))
end GJKKL.TrackHyp

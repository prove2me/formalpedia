-- Prove2me | solution 1 for GJKKL.TrackHyp.card_sdiff_Dv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:59.812152+00:00
-- url     : https://prove2.me/submissions/a51e3229-9d67-406a-9698-36ff1419634f

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
    ((avail H h \ Dv H h v).card : ℝ) = (avail H h).card - dv H h v := by
  have hsub : Dv H h v ⊆ avail H h := filter_subset _ _
  rw [card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]
  rfl
end GJKKL.TrackHyp

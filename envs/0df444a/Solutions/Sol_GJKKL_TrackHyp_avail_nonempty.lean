-- Prove2me | solution 1 for GJKKL.TrackHyp.avail_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:19.004241+00:00
-- url     : https://prove2.me/submissions/58e3a9ed-da3a-4bf2-823c-6d88806c0c6f

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Theorems.Thm_GJKKL_TrackHyp_aP_pos
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
theorem _root_.solution {h : List (Finset V)} (hT : h.length < T) (hh : IsGreedySeq H h)
    (ht : Tracked H dh δ h) : (avail H h).Nonempty := by
  have h1 := (hyp.avail_bounds hh ht).1
  have hpos : 0 < aPar V k h.length * (dh h.length - δ h.length) :=
    mul_pos (hyp.aP_pos hT) (by linarith [hyp.δ_le _ hT, hyp.dh_pos _ hT])
  have : (0 : ℝ) < (avail H h).card := hpos.trans_le h1
  exact card_pos.mp (by exact_mod_cast this)
end GJKKL.TrackHyp

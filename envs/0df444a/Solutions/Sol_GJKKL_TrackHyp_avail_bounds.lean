-- Prove2me | solution 1 for GJKKL.TrackHyp.avail_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:38.056933+00:00
-- url     : https://prove2.me/submissions/ddeb879e-ad3a-4c99-9c1c-85be9364b9e3

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Theorems.Thm_GJKKL_TrackHyp_k_pos
public import Theorems.Thm_GJKKL_card_avail_bounds


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
theorem _root_.solution {h : List (Finset V)} (hh : IsGreedySeq H h) (ht : Tracked H dh δ h) :
    aPar V k h.length * (dh h.length - δ h.length) ≤ (avail H h).card ∧
      ((avail H h).card : ℝ) ≤ aPar V k h.length * (dh h.length + δ h.length) :=
  card_avail_bounds H hyp.unif hyp.k_pos hh ht
end GJKKL.TrackHyp

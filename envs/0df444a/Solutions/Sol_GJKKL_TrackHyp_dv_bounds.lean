-- Prove2me | solution 1 for GJKKL.TrackHyp.dv_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:44:10.95886+00:00
-- url     : https://prove2.me/submissions/b781ba63-dd39-4d38-999b-410bc997d06c

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
theorem _root_.solution {h : List (Finset V)} (ht : Tracked H dh δ h) {v : V} (hv : v ∉ covered h) :
    dh h.length - δ h.length ≤ (dv H h v : ℝ) ∧ (dv H h v : ℝ) ≤ dh h.length + δ h.length := by
  have := ht v hv
  rw [abs_le] at this
  constructor <;> linarith
end GJKKL.TrackHyp

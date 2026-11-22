-- Prove2me | solution 1 for GJKKL.TrackHyp.mass_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:52.598932+00:00
-- url     : https://prove2.me/submissions/65234014-00e7-4fe8-a858-a3f3ee344dab

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Theorems.Thm_GJKKL_greedyKernel_mass_eq_one


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
theorem _root_.solution {h : List (Finset V)} (hg : GoodState H dh δ h) :
    ∑ a, (greedyKernel H).K h a = 1 :=
  greedyKernel_mass_eq_one hg.2.2
end GJKKL.TrackHyp

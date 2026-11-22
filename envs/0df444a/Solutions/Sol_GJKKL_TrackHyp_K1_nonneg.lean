-- Prove2me | solution 1 for GJKKL.TrackHyp.K1_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:42:24.851885+00:00
-- url     : https://prove2.me/submissions/11ddda9a-a0b0-4873-8711-4d71c6b4452f

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Theorems.Thm_GJKKL_TrackHyp_k_pos

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
theorem _root_.solution : (0 : ℝ) ≤ (k : ℝ) - 1 := by
  have : (1 : ℝ) ≤ k := by exact_mod_cast hyp.k_pos
  linarith
end GJKKL.TrackHyp

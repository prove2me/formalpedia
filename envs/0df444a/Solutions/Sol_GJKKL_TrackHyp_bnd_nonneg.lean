-- Prove2me | solution 1 for GJKKL.TrackHyp.bnd_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:01.583867+00:00
-- url     : https://prove2.me/submissions/0a01f93d-fd09-47bc-8a29-d6fac836e645

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Theorems.Thm_GJKKL_bnd_def
public import Theorems.Thm_GJKKL_TrackHyp_aP_pos
public import Theorems.Thm_GJKKL_TrackHyp_r_nonneg
public import Theorems.Thm_GJKKL_TrackHyp_K1_nonneg

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
theorem _root_.solution {t : ℕ} (ht : t < T) : 0 ≤ bnd V k dh δ t := by
  rw [bnd_def]
  have hL : 0 < dh t - δ t := by linarith [hyp.δ_le t ht, hyp.dh_pos t ht]
  have := hyp.g_nonneg t ht
  have := hyp.r_nonneg ht
  have : 0 ≤ ((k : ℝ) - 1) * (dh t + δ t) ^ 2 / (aPar V k t * (dh t - δ t)) :=
    div_nonneg (mul_nonneg hyp.K1_nonneg (sq_nonneg _)) (mul_pos (hyp.aP_pos ht) hL).le
  linarith
end GJKKL.TrackHyp

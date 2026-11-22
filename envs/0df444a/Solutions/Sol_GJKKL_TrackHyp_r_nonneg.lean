-- Prove2me | solution 1 for GJKKL.TrackHyp.r_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:42:59.981444+00:00
-- url     : https://prove2.me/submissions/275da736-e99b-4f86-8c70-bea2828f0359

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Theorems.Thm_GJKKL_TrackHyp_k_pos
public import Theorems.Thm_GJKKL_TrackHyp_aP_pos

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
theorem _root_.solution {t : ℕ} (ht : t < T) : 0 ≤ δ (t + 1) - δ t := by
  have hB : 0 ≤ B := by linarith [hyp.B_ge, show (1 : ℝ) ≤ k by exact_mod_cast hyp.k_pos]
  exact le_trans (div_nonneg (mul_nonneg hB (hyp.δ_nonneg t ht)) (hyp.aP_pos ht).le)
    (hyp.r_ge t ht)
end GJKKL.TrackHyp

-- Prove2me | solution 1 for Csg.DiscountedCSG.valueIteration_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:24:47.852629+00:00
-- url     : https://prove2.me/submissions/a0bc0beb-0b9a-4439-8ed9-00ab31324011

import Definitions.Def_Csg_Discounted
import Definitions.Def_Csg_DiscountedValueIteration
import Theorems.Thm_Csg_DiscountedCSG_vOpt_fixedPoint
import Theorems.Thm_Csg_DiscountedCSG_shapley_aposteriori_bound
import Theorems.Thm_Csg_DiscountedCSG_numIters_spec
import Theorems.Thm_Csg_DiscountedCSG_shapley_contracting


set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)
namespace Csg.DiscountedCSG
theorem _root_.solution {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) :
    2 * dist (D.valueIteration eps v) D.vOpt < eps := by
  have hval : D.valueIteration eps v = D.shapley^[D.numIters heps v + 1] v := by
    simp only [valueIteration, dif_pos heps]
  have hstop : 2 * D.l * dist (D.shapley^[D.numIters heps v + 1] v)
      (D.shapley^[D.numIters heps v] v) < eps * (1 - D.l) :=
    D.numIters_spec heps v
  set N := D.numIters heps v
  set w := D.shapley^[N] v with hw
  have hbw : D.shapley^[N + 1] v = D.shapley w := by
    rw [hw]; exact Function.iterate_succ_apply' D.shapley N v
  rw [hbw] at hval hstop
  rw [dist_comm (D.shapley w) w] at hstop
  rw [hval]
  have hlcast : (D.lNN : ℝ) = D.l := rfl
  have hbound : dist w D.vOpt ≤ dist w (D.shapley w) / (1 - D.l) := by
    have h0 := D.shapley_aposteriori_bound w 0
    simp only [Function.iterate_zero_apply, zero_add, Function.iterate_one] at h0
    rwa [hlcast] at h0
  have hopt_move : dist w D.vOpt * (1 - D.l) ≤ dist w (D.shapley w) := by
    rw [le_div_iff₀ (by linarith [D.l_lt_one] : (0 : ℝ) < 1 - D.l)] at hbound
    exact hbound
  have hcontract : dist (D.shapley w) D.vOpt ≤ D.l * dist w D.vOpt := by
    have h1 := D.shapley_contracting w D.vOpt
    rwa [D.vOpt_fixedPoint] at h1
  have step1 : (2 * D.l * dist w D.vOpt) * (1 - D.l) ≤ 2 * D.l * dist w (D.shapley w) := by
    nlinarith [hopt_move, D.l_nonneg]
  have step2 : (2 * D.l * dist w D.vOpt) * (1 - D.l) < eps * (1 - D.l) := by
    nlinarith [step1, hstop]
  have step3 : 2 * D.l * dist w D.vOpt < eps :=
    lt_of_mul_lt_mul_right step2 (by linarith [D.l_lt_one] : (0 : ℝ) ≤ 1 - D.l)
  linarith [hcontract, step3]
end Csg.DiscountedCSG

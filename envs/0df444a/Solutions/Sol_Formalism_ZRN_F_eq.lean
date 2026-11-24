-- Prove2me | solution 1 for Formalism.ZRN.F_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:29:41.282094+00:00
-- url     : https://prove2.me/submissions/cb2147dc-c167-4577-9219-c691372b7603

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Theorems.Thm_Formalism_ZRN_norm_cpow_nat
import Theorems.Thm_Formalism_ZRN_summable_e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism
open Formalism.ZRN
namespace Formalism.ZRN
theorem _root_.solution (s : ℂ) (h : 1 < s.re) : F s = 1 + (1 - s) * riemannZeta s := by
  have hS := summable_e s (by linarith)
  have hz : riemannZeta s = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s := zeta_eq_tsum_one_div_nat_add_one_cpow h
  have hA : Summable (fun n : ℕ => (1 - s) * ((n : ℂ) + 1) ^ (-s)) := by
    have := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr h)
    refine (this.mul_left (1 - s)).congr (fun n => ?_)
    push_cast; rw [cpow_neg, one_div]
  have hB : Summable (fun n : ℕ => ((n : ℂ) + 1) ^ (1 - s) - ((n : ℂ) + 2) ^ (1 - s)) := by
    refine (hS.sub hA).congr (fun n => ?_); simp only [e]; ring
  have hp : ∀ N : ℕ, ∑ n ∈ Finset.range N, (((n : ℂ) + 1) ^ (1 - s) - ((n : ℂ) + 2) ^ (1 - s))
      = 1 - ((N : ℂ) + 1) ^ (1 - s) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring_nf
  have hlim0 : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (1 - s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e1 : ∀ N : ℕ, ‖((N : ℂ) + 1) ^ (1 - s)‖ = ((N : ℝ) + 1) ^ (1 - s.re) := by
      intro N
      have := norm_cpow_nat N 1 (by positivity) (1 - s)
      push_cast at this; simpa using this
    simp_rw [e1]
    have hN : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have := (tendsto_rpow_neg_atTop (y := s.re - 1) (by linarith)).comp hN
    refine this.congr (fun N => ?_)
    simp only [Function.comp_apply, neg_sub]
  have htB : ∑' n : ℕ, (((n : ℂ) + 1) ^ (1 - s) - ((n : ℂ) + 2) ^ (1 - s)) = 1 := by
    have ht := hB.hasSum.tendsto_sum_nat
    simp_rw [hp] at ht
    have hlim : Tendsto (fun N : ℕ => 1 - ((N : ℂ) + 1) ^ (1 - s)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hlim0
    exact tendsto_nhds_unique ht hlim
  unfold F
  calc ∑' n, e n s
      = ∑' n : ℕ, ((1 - s) * ((n : ℂ) + 1) ^ (-s)
          + (((n : ℂ) + 1) ^ (1 - s) - ((n : ℂ) + 2) ^ (1 - s))) := by
        refine tsum_congr (fun n => ?_); simp only [e]; ring
    _ = (1 - s) * riemannZeta s + 1 := by
        rw [hA.tsum_add hB, htB, tsum_mul_left, hz]
        congr 2
        refine tsum_congr (fun n => ?_)
        rw [cpow_neg, one_div]
    _ = 1 + (1 - s) * riemannZeta s := by ring
end Formalism.ZRN

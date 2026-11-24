-- Prove2me | solution 1 for Formalism.ZRN.e_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:56:15.623883+00:00
-- url     : https://prove2.me/submissions/45877822-a49d-4eb1-b5cd-b6299b4b93a9

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Theorems.Thm_Formalism_ZRN_e_bound
import Theorems.Thm_Formalism_ZRN_e_crude

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
theorem _root_.solution (s₀ : ℂ) (h : 0 < s₀.re) : ∃ r > 0, ∃ u : ℕ → ℝ, Summable u ∧
    ∀ n : ℕ, ∀ w ∈ Metric.ball s₀ r, ‖e n w‖ ≤ u n := by
  set δ := s₀.re / 2 with hδ
  set R := ‖1 - s₀‖ + 1 with hR
  have hδ0 : 0 < δ := by positivity
  have hR0 : 0 ≤ R := by positivity
  refine ⟨min δ 1, lt_min hδ0 one_pos,
    fun n => (R ^ 2 + R) * ((n : ℝ) + 1) ^ (-1 - δ) +
      (if (n : ℝ) + 1 < R then R + 2 * ((n : ℝ) + 1) + 1 else 0), ?_, ?_⟩
  · refine Summable.add ?_ ?_
    · refine Summable.mul_left _ ?_
      have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -1 - δ < -1))
      refine this.congr (fun n => ?_)
      push_cast; ring_nf
    · refine summable_of_ne_finset_zero (s := Finset.range ⌈R⌉₊) (fun n hn => ?_)
      rw [Finset.mem_range, not_lt] at hn
      have : R ≤ (n : ℝ) := (Nat.le_ceil R).trans (by exact_mod_cast hn)
      rw [if_neg (by linarith)]
  · intro n w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hwr : ‖w - s₀‖ < δ := lt_of_lt_of_le hw (min_le_left _ _)
    have hw1 : ‖w - s₀‖ < 1 := lt_of_lt_of_le hw (min_le_right _ _)
    have hre : δ < w.re := by
      have := Complex.abs_re_le_norm (w - s₀)
      rw [Complex.sub_re] at this
      have := (abs_le.mp this).1
      linarith
    have hnorm : ‖1 - w‖ ≤ R := by
      calc ‖1 - w‖ = ‖(1 - s₀) - (w - s₀)‖ := by ring_nf
        _ ≤ ‖1 - s₀‖ + ‖w - s₀‖ := norm_sub_le _ _
        _ ≤ R := by linarith
    have hx : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := n.cast_nonneg (α := ℝ); linarith
    have hfirst : 0 ≤ (R ^ 2 + R) * ((n : ℝ) + 1) ^ (-1 - δ) := by positivity
    show ‖e n w‖ ≤ (R ^ 2 + R) * ((n : ℝ) + 1) ^ (-1 - δ) +
      (if (n : ℝ) + 1 < R then R + 2 * ((n : ℝ) + 1) + 1 else 0)
    by_cases hc : (n : ℝ) + 1 < R
    · rw [if_pos hc]
      have := e_crude n w (by linarith)
      linarith
    · rw [if_neg hc, add_zero]
      replace hc := not_lt.mp hc
      refine (e_bound n w (hnorm.trans hc)).trans ?_
      have hp : ((n : ℝ) + 1) ^ (-1 - w.re) ≤ ((n : ℝ) + 1) ^ (-1 - δ) :=
        Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      have hq : ‖1 - w‖ ^ 2 + ‖1 - w‖ ≤ R ^ 2 + R := by
        have := norm_nonneg (1 - w)
        nlinarith
      exact mul_le_mul hq hp (by positivity) (by positivity)
end Formalism.ZRN

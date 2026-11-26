-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.eventually_unit_ball_subset_iterate_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:34.368636+00:00
-- url     : https://prove2.me/submissions/ca9e7253-ebaa-45f5-a912-92ff3e05dc72

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_RealAxis
import Definitions.Def_ExpChaotic_Covering
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exp_ball_real_expands
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_real_orbit
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {x : ℂ} (hx : x.im = 0)
    (hx2 : 2 ≤ x.re) {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, ∀ n ≥ N, ball (expIterate n x) 1 ⊆ expIterate n '' ball x r := by
  -- Double the guaranteed radius at each step, capping it at one to preserve injectivity.
  have hballs : ∀ n : ℕ,
      ball (expIterate n x) (min (r * 2 ^ n) 1) ⊆ expIterate n '' ball x r := by
    intro n
    induction n with
    | zero =>
        simpa using (ball_subset_ball (min_le_left r 1) : ball x (min r 1) ⊆ ball x r)
    | succ n ih =>
        have hpos : 0 < min (r * (2 : ℝ) ^ n) 1 := by positivity
        have hg := exp_ball_real_expands (expIterate_real_orbit hx n).1
          hpos (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 2)
          (by linarith [(expIterate_real_orbit hx n).2, Nat.cast_nonneg (α := ℝ) n])
        have hrad : min (r * (2 : ℝ) ^ (n + 1)) 1 ≤ min (r * 2 ^ n) 1 * 2 := by
          rw [pow_succ, ← mul_assoc]
          rcases le_total (r * (2 : ℝ) ^ n) 1 with h | h
          · rw [min_eq_left h]
            exact min_le_left _ _
          · rw [min_eq_right h]
            exact (min_le_right _ _).trans (by norm_num)
        intro y hy
        rw [expIterate_succ] at hy
        obtain ⟨z, hz, rfl⟩ := hg ((ball_subset_ball hrad) hy)
        obtain ⟨w, hw, rfl⟩ := ih hz
        exact ⟨w, hw, expIterate_succ n w⟩
  -- Eventually the cap is reached and every subsequent image contains a unit disk.
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / r)
  refine ⟨N, fun n hn => ?_⟩
  have hpow : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n := n)))
  have hlarge : 1 ≤ r * (2 : ℝ) ^ n := by
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
    have : 1 / r < (2 : ℝ) ^ n := lt_of_lt_of_le hN (hcast.trans hpow)
    exact (le_of_lt ((div_lt_iff₀ hr).mp this)).trans_eq (mul_comm _ _)
  simpa only [min_eq_right hlarge] using hballs n
end ExponentialJuliaSetMisiurewicz

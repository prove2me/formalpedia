-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.closing_inverse_on_small_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:41.832959+00:00
-- url     : https://prove2.me/submissions/d1987554-bb6e-4458-a50d-1ede2a3da283

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Periodic
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_lipschitz_local_inverse
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_closing_inverse
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
theorem _root_.solution {a : ℂ} (ha : a ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ε ∧ ∃ C : ℝ≥0, ∃ ρ : ℝ,
      ∀ x : ℝ, ρ ≤ x → ∃ ψ : ℂ → ℂ,
        LipschitzOnWith C ψ (closedBall a r) ∧
        MapsTo ψ (closedBall a r) (ball (x : ℂ) 8) ∧
        ∀ z ∈ closedBall a r, expIterate 2 (ψ z) = z := by
  have hsd : HasStrictDerivAt Complex.exp (deriv Complex.exp (Complex.log a)) (Complex.log a) := by
    simpa only [Complex.deriv_exp] using Complex.hasStrictDerivAt_exp (Complex.log a)
  obtain ⟨L, C, s, hs, _, hL, hinv⟩ := exists_lipschitz_local_inverse hsd
    (by simpa only [Complex.deriv_exp] using Complex.exp_ne_zero (Complex.log a))
  rw [Complex.exp_log ha] at hL hinv
  -- Shrink the source disk so the chosen logarithm branch varies by at most one.
  let r : ℝ := min ε (min (s / 2) (1 / ((C : ℝ) + 1)))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : r ≤ ε := min_le_left _ _
  have hrs : r ≤ s / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrC : r * ((C : ℝ) + 1) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_right _ _))
  have hsub : closedBall a r ⊆ ball a s :=
    closedBall_subset_ball (by linarith)
  have hsmall : ∀ z ∈ closedBall a r, ‖L z - L a‖ ≤ 1 := by
    intro z hz
    have h := hL.norm_sub_le (hsub hz) (mem_ball_self hs)
    have hz' : ‖z - a‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
    have hh := mul_le_mul_of_nonneg_left hz' C.coe_nonneg
    nlinarith
  obtain ⟨ρ, hρ⟩ := exists_closing_inverse
    (hL.mono hsub) hsmall (fun z hz => hinv z (hsub hz))
  exact ⟨r, hr, hrε, C, ρ, hρ⟩
end ExponentialJuliaSetMisiurewicz

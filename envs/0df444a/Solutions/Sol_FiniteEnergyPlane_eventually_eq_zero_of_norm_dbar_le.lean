-- Prove2me | solution 1 for FiniteEnergyPlane.eventually_eq_zero_of_norm_dbar_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-05T20:55:03.95337+00:00
-- url     : https://prove2.me/submissions/b1faa35c-fc3d-49d8-a214-a94482070571

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Theorems.Thm_JHolomorphic_exists_factorization_of_norm_dbar_le

open Metric Filter Topology
open scoped ContDiff

namespace FiniteEnergyPlane

theorem eventually_eq_zero_of_norm_dbar_le_aux (g : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (M : ℝ)
    (hM : ∀ z ∈ U, ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) (hacc : ∃ᶠ z in 𝓝[≠] z₀, g z = 0) :
    ∀ᶠ z in 𝓝 z₀, g z = 0 := by
  set A : ℂ →L[ℝ] ℂ := Complex.I • ContinuousLinearMap.id ℝ ℂ with hAdef
  have hAapp : ∀ x, A x = Complex.I * x := fun x => by simp [hAdef]
  have hA2 : A.comp A = -ContinuousLinearMap.id ℝ ℂ := by
    ext x <;> simp [hAapp, ← mul_assoc]
  have hn : Module.finrank ℝ ℂ = 2 * 1 := by simp [Complex.finrank_real_complex]
  obtain ⟨ε, hε, hεU, Θ, f, hΘc, hΘb, hf, hgf⟩ :=
    JHolomorphic.exists_factorization_of_norm_dbar_le 1 hn (fun _ => A) U hU contDiffOn_const
      (fun _ _ => hA2) g hg M (fun z hz => by simpa only [hAapp] using hM z hz) z₀ hz₀
  have hz₀ε : z₀ ∈ ball z₀ ε := mem_ball_self hε
  have hnh : ball z₀ ε ∈ 𝓝 z₀ := isOpen_ball.mem_nhds hz₀ε
  have hfa : AnalyticAt ℂ f z₀ := hf.analyticAt hnh
  have hf0 : ∃ᶠ z in 𝓝[≠] z₀, f z = 0 := by
    have hnh' : ∀ᶠ z in 𝓝[≠] z₀, z ∈ ball z₀ ε := mem_nhdsWithin_of_mem_nhds hnh
    refine (hacc.and_eventually hnh').mono ?_
    rintro z ⟨hgz, hzε⟩
    apply (hΘb z (ball_subset_closedBall hzε)).1.1
    rw [map_zero, ← hgf z hzε, hgz]
  have hfe := hfa.frequently_zero_iff_eventually_zero.1 hf0
  filter_upwards [hfe, hnh] with z hz hzε
  rw [hgf z hzε, hz, map_zero]

end FiniteEnergyPlane

open FiniteEnergyPlane

open Filter Topology
open scoped ContDiff

theorem solution (g : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (M : ℝ)
    (hM : ∀ z ∈ U, ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) (hacc : ∃ᶠ z in 𝓝[≠] z₀, g z = 0) :
    ∀ᶠ z in 𝓝 z₀, g z = 0 :=
  eventually_eq_zero_of_norm_dbar_le_aux g U hU hg M hM z₀ hz₀ hacc

-- Prove2me | solution 1 for FiniteEnergyPlane.exists_hasLoopWind_of_norm_dbar_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-05T20:23:02.884424+00:00
-- url     : https://prove2.me/submissions/6042b6c7-da35-48db-8090-f469759bad68

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Theorems.Thm_FiniteEnergyPlane_exists_ball_hasLoopWind_re_mul_add_im_mul
import Theorems.Thm_JHolomorphic_exists_factorization_of_norm_dbar_le

open Metric Filter Topology
open scoped ContDiff

namespace FiniteEnergyPlane

theorem exists_hasLoopWind_of_norm_dbar_le_aux (g : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (M : ℝ)
    (hM : ∀ z ∈ U, ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) (hg₀ : g z₀ = 0) (hiso : ∀ z ∈ U, g z = 0 → z = z₀) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ r > (0 : ℝ), ∀ ρ ∈ Set.Ioo 0 r,
      HasLoopWind (fun t => g (z₀ + ccwLoop ρ t)) m := by
  set A : ℂ →L[ℝ] ℂ := Complex.I • ContinuousLinearMap.id ℝ ℂ with hAdef
  have hAapp : ∀ x, A x = Complex.I * x := fun x => by simp [hAdef]
  have hA2 : A.comp A = -ContinuousLinearMap.id ℝ ℂ := by
    ext x <;> simp [hAapp, ← mul_assoc]
  have hn : Module.finrank ℝ ℂ = 2 * 1 := by simp [Complex.finrank_real_complex]
  obtain ⟨ε, hε, hεU, Θ, f, hΘc, hΘb, hf, hgf⟩ :=
    JHolomorphic.exists_factorization_of_norm_dbar_le 1 hn (fun _ => A) U hU contDiffOn_const
      (fun _ _ => hA2) g hg M (fun z hz => by simpa only [hAapp] using hM z hz) z₀ hz₀
  have hz₀ε : z₀ ∈ ball z₀ ε := mem_ball_self hε
  have hfa : AnalyticAt ℂ f z₀ := hf.analyticAt (isOpen_ball.mem_nhds hz₀ε)
  have h0 : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0 := by
    intro h
    obtain ⟨r, hr, hrs⟩ := Metric.eventually_nhds_iff_ball.1 (h.and (isOpen_ball.mem_nhds hz₀ε))
    have hne : z₀ + (r / 2 : ℝ) ≠ z₀ := by
      simp [hr.ne']
    have hmem : z₀ + (r / 2 : ℝ) ∈ ball z₀ r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hr)]
      exact half_lt_self hr
    obtain ⟨hfz, hzε⟩ := hrs _ hmem
    exact hne (hiso _ (hεU hzε) (by rw [hgf _ hzε, hfz, map_zero]))
  obtain ⟨m, e, hea, he0, hfe⟩ := hfa.exists_eventuallyEq_pow_smul_nonzero_iff.2 h0
  obtain ⟨r₁, hr₁, hr₁s⟩ := Metric.eventually_nhds_iff_ball.1
    ((hfe.and hea.eventually_analyticAt).and (isOpen_ball.mem_nhds hz₀ε))
  set R := min r₁ ε with hRdef
  have hR : 0 < R := lt_min hr₁ hε
  have hRε : ball z₀ R ⊆ ball z₀ ε := ball_subset_ball (min_le_right _ _)
  have hRr : ball z₀ R ⊆ ball z₀ r₁ := ball_subset_ball (min_le_left _ _)
  set p : ℂ → ℂ := fun z => Θ z (e z) with hpdef
  set q : ℂ → ℂ := fun z => Complex.I * p z with hqdef
  have hΘI : ∀ z ∈ ball z₀ ε, ∀ w, Θ z (Complex.I • w) = Complex.I * Θ z w := fun z hz w => by
    rw [(hΘb z (ball_subset_closedBall hz)).2 w, hAapp]
  have hFpq : ∀ z ∈ ball z₀ R, g z =
      (((z - z₀) ^ m).re : ℂ) * p z + (((z - z₀) ^ m).im : ℂ) * q z := by
    intro z hz
    have hzε := hRε hz
    rw [hgf z hzε, ((hr₁s z (hRr hz)).1).1]
    set w := (z - z₀) ^ m
    have hw : w • e z = ((w.re : ℝ) : ℂ) • e z + ((w.im : ℝ) : ℂ) • (Complex.I • e z) := by
      rw [smul_smul, ← add_smul]
      congr 1
      exact (Complex.re_add_im w).symm
    rw [hw, map_add, Complex.coe_smul, Complex.coe_smul, map_smul, map_smul, hΘI z hzε]
    simp only [hpdef, hqdef, Complex.real_smul]
  have hpc : ContinuousOn p (ball z₀ R) := fun z hz => by
    have hzε := hRε hz
    have hΘz : ContinuousAt Θ z := hΘc.continuousAt (closedBall_mem_nhds_of_mem hzε)
    exact (hΘz.clm_apply ((hr₁s z (hRr hz)).1.2).continuousAt).continuousWithinAt
  have hqc : ContinuousOn q (ball z₀ R) := continuousOn_const.mul hpc
  have hp0 : p z₀ ≠ 0 := by
    intro h
    apply he0
    apply (hΘb z₀ (mem_closedBall_self hε.le)).1.1
    rw [map_zero]
    exact h
  have hpq : 0 < (starRingEnd ℂ (p z₀) * q z₀).im := by
    have h1 : starRingEnd ℂ (p z₀) * q z₀ = Complex.I * ((‖p z₀‖ ^ 2 : ℝ) : ℂ) := by
      simp only [hqdef]
      rw [mul_left_comm, Complex.conj_mul']
      push_cast
      rfl
    rw [h1, Complex.mul_im]
    simp only [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul,
      zero_add]
    have := norm_pos_iff.2 hp0
    positivity
  obtain ⟨r, hr, -, -, hwind⟩ :=
    exists_ball_hasLoopWind_re_mul_add_im_mul g p q z₀ R hR m hpc hqc hpq hFpq
  refine ⟨m, ?_, r, hr, fun ρ hρ => hwind ρ hρ⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exfalso
    have h1 := hFpq z₀ (mem_ball_self hR)
    rw [hm, pow_zero, Complex.one_re, Complex.one_im, hg₀] at h1
    simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, add_zero] at h1
    exact hp0 h1.symm
  · exact hm

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped ContDiff

theorem solution (g : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (M : ℝ)
    (hM : ∀ z ∈ U, ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) (hg₀ : g z₀ = 0) (hiso : ∀ z ∈ U, g z = 0 → z = z₀) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ r > (0 : ℝ), ∀ ρ ∈ Set.Ioo 0 r,
      HasLoopWind (fun t => g (z₀ + ccwLoop ρ t)) m :=
  FiniteEnergyPlane.exists_hasLoopWind_of_norm_dbar_le_aux g U hU hg M hM z₀ hz₀ hg₀ hiso

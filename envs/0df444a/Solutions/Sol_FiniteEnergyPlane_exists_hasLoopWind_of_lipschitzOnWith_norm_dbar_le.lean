-- Prove2me | solution 1 for FiniteEnergyPlane.exists_hasLoopWind_of_lipschitzOnWith_norm_dbar_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-27T00:29:27.5158+00:00
-- url     : https://prove2.me/submissions/8099f93d-2a63-4698-aa3a-e0cbd27480f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Theorems.Thm_FiniteEnergyPlane_exists_ball_hasLoopWind_re_mul_add_im_mul
import Theorems.Thm_JHolomorphic_exists_factorization_of_lipschitzOnWith_norm_dbar_le

open Metric MeasureTheory Filter Topology
open scoped NNReal

namespace FiniteEnergyPlane

/-- Zeros of Lipschitz functions with `|∂̄g| ≤ M|g|` a.e. are isolated and wind positively. -/
theorem exists_hasLoopWind_of_lipschitzOnWith_aux (g : ℂ → ℂ) (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ℝ≥0) (hg : LipschitzOnWith K g (ball z₀ ρ)) (M : ℝ)
    (hM : ∀ᵐ z ∂(volume.restrict (ball z₀ ρ)),
      ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖)
    (hg₀ : g z₀ = 0) (hfreq : ∃ᶠ z in 𝓝 z₀, g z ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ r > (0 : ℝ), r ≤ ρ ∧ (∀ z ∈ ball z₀ r, z ≠ z₀ → g z ≠ 0) ∧
      ∀ ρ' ∈ Set.Ioo 0 r, HasLoopWind (fun t => g (z₀ + ccwLoop ρ' t)) m := by
  obtain ⟨ε, hε, hερ, θ, f, hθc, hθ0, hf, hgf⟩ :=
    JHolomorphic.exists_factorization_of_lipschitzOnWith_norm_dbar_le g z₀ ρ hρ K hg M hM
  have hz₀ε : z₀ ∈ ball z₀ ε := mem_ball_self hε
  have hfa : AnalyticAt ℂ f z₀ := hf.analyticAt (isOpen_ball.mem_nhds hz₀ε)
  have h0 : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0 := by
    intro h
    have hev : ∀ᶠ z in 𝓝 z₀, g z = 0 := by
      filter_upwards [h, isOpen_ball.mem_nhds hz₀ε] with z hz hzε
      rw [hgf z hzε, hz, mul_zero]
    exact hfreq.and_eventually hev |>.exists.elim fun _ h => h.1 h.2
  obtain ⟨m, e, hea, he0, hfe⟩ := hfa.exists_eventuallyEq_pow_smul_nonzero_iff.2 h0
  obtain ⟨r₁, hr₁, hr₁s⟩ := Metric.eventually_nhds_iff_ball.1
    ((hfe.and hea.eventually_analyticAt).and (isOpen_ball.mem_nhds hz₀ε))
  set R := min r₁ ε with hRdef
  have hR : 0 < R := lt_min hr₁ hε
  have hRε : ball z₀ R ⊆ ball z₀ ε := ball_subset_ball (min_le_right _ _)
  have hRr : ball z₀ R ⊆ ball z₀ r₁ := ball_subset_ball (min_le_left _ _)
  set p : ℂ → ℂ := fun z => θ z * e z with hpdef
  set q : ℂ → ℂ := fun z => Complex.I * p z with hqdef
  have hFpq : ∀ z ∈ ball z₀ R, g z =
      (((z - z₀) ^ m).re : ℂ) * p z + (((z - z₀) ^ m).im : ℂ) * q z := by
    intro z hz
    have hzε := hRε hz
    rw [hgf z hzε, ((hr₁s z (hRr hz)).1).1, smul_eq_mul]
    simp only [hpdef, hqdef]
    have h := Complex.re_add_im ((z - z₀) ^ m)
    linear_combination (θ z * e z) * h.symm
  have hpc : ContinuousOn p (ball z₀ R) := fun z hz => by
    have hzε := hRε hz
    have hθz : ContinuousAt θ z := hθc.continuousAt (closedBall_mem_nhds_of_mem hzε)
    exact (hθz.mul ((hr₁s z (hRr hz)).1.2).continuousAt).continuousWithinAt
  have hqc : ContinuousOn q (ball z₀ R) := continuousOn_const.mul hpc
  have hp0 : p z₀ ≠ 0 := mul_ne_zero (hθ0 z₀ (mem_closedBall_self hε.le)) he0
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
  obtain ⟨r, hr, hrR, hiso, hwind⟩ :=
    exists_ball_hasLoopWind_re_mul_add_im_mul g p q z₀ R hR m hpc hqc hpq hFpq
  have hRρ : R ≤ ρ := (min_le_right _ _).trans hερ.le
  refine ⟨m, ?_, r, hr, hrR.trans hRρ, hiso, fun ρ' hρ' => hwind ρ' hρ'⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exfalso
    have h1 := hFpq z₀ (mem_ball_self hR)
    rw [hm, pow_zero, Complex.one_re, Complex.one_im, hg₀] at h1
    simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, add_zero] at h1
    exact hp0 h1.symm
  · exact hm

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution (g : ℂ → ℂ) (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ℝ≥0) (hg : LipschitzOnWith K g (ball z₀ ρ)) (M : ℝ)
    (hM : ∀ᵐ z ∂(volume.restrict (ball z₀ ρ)),
      ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖)
    (hg₀ : g z₀ = 0) (hfreq : ∃ᶠ z in 𝓝 z₀, g z ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ r > (0 : ℝ), r ≤ ρ ∧ (∀ z ∈ ball z₀ r, z ≠ z₀ → g z ≠ 0) ∧
      ∀ ρ' ∈ Set.Ioo 0 r, HasLoopWind (fun t => g (z₀ + ccwLoop ρ' t)) m :=
  exists_hasLoopWind_of_lipschitzOnWith_aux g z₀ ρ hρ K hg M hM hg₀ hfreq

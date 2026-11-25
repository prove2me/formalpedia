-- Prove2me | solution 1 for FiniteEnergyPlane.exists_contDiffOn_log_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T13:32:49.441823+00:00
-- url     : https://prove2.me/submissions/9d5d562b-b517-4e17-8bbb-e9c01e35722b

import Mathlib



namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

theorem exists_contDiffOn_log_eq_aux {l : ℕ} {η : ℝ} (hη : 0 < η) {A : ℝ → ℂ} (hA : ContDiffOn ℝ l A (ball 0 η))
    (hA0 : A 0 ≠ 0) : ∃ ρ > 0, ρ ≤ η ∧ ∃ f : ℝ → ℂ, ContDiffOn ℝ l f (ball 0 ρ) ∧
      ∀ s ∈ ball (0 : ℝ) ρ, Complex.exp (f s) = A s := by
  have hc : ContinuousAt (fun s => A s / A 0) 0 :=
    (hA.continuousOn.continuousAt (ball_mem_nhds 0 hη)).div_const _
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), A s / A 0 ∈ Complex.slitPlane :=
    hc (Complex.isOpen_slitPlane.mem_nhds (by simp [hA0]))
  obtain ⟨ρ, hρ, hs⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨min ρ η, lt_min hρ hη, min_le_right _ _,
    fun s => Complex.log (A 0) + Complex.log (A s / A 0), ?_, ?_⟩
  · refine contDiffOn_const.add ?_
    intro s hs'
    have h1 : s ∈ ball (0 : ℝ) ρ := ball_subset_ball (min_le_left _ _) hs'
    have h2 : s ∈ ball (0 : ℝ) η := ball_subset_ball (min_le_right _ _) hs'
    have h3 : ContDiffAt ℝ l (fun s => A s / A 0) s :=
      (hA.contDiffAt (isOpen_ball.mem_nhds h2)).div_const _
    have h4 : ContDiffAt ℝ l Complex.log (A s / A 0) :=
      ((Complex.contDiffAt_log (n := l) (hs s h1)).restrict_scalars ℝ)
    exact (h4.comp s h3).contDiffWithinAt
  · intro s hs'
    have h1 : s ∈ ball (0 : ℝ) ρ := ball_subset_ball (min_le_left _ _) hs'
    rw [Complex.exp_add, Complex.exp_log hA0, Complex.exp_log (Complex.slitPlane_ne_zero (hs s h1)),
      mul_div_cancel₀ _ hA0]

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

theorem solution {l : ℕ} {η : ℝ} (hη : 0 < η) {A : ℝ → ℂ} (hA : ContDiffOn ℝ l A (ball 0 η))
    (hA0 : A 0 ≠ 0) : ∃ ρ > 0, ρ ≤ η ∧ ∃ f : ℝ → ℂ, ContDiffOn ℝ l f (ball 0 ρ) ∧
      ∀ s ∈ ball (0 : ℝ) ρ, Complex.exp (f s) = A s :=
  exists_contDiffOn_log_eq_aux hη hA hA0

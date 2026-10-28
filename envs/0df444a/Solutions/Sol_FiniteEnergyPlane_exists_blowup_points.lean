-- Prove2me | solution 1 for FiniteEnergyPlane.exists_blowup_points
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-25T18:03:50.220839+00:00
-- url     : https://prove2.me/submissions/fd12f727-57c7-4c28-a2d7-7d96008c333b

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_hofer_lemma
import Mathlib.Analysis.SpecialFunctions.Sqrt



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Blow-up points with doubling control on shrinking discs. -/
theorem exists_blowup_points_aux (g : ℕ → ℂ → ℝ) (U : ℕ → Set ℂ) (z : ℕ → ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (hball : ∀ k, closedBall (z k) ρ ⊆ U k) (hg : ∀ k, ContinuousOn (g k) (U k))
    (hg0 : ∀ k w, 0 ≤ g k w) (hpos : ∀ k, 0 < g k (z k))
    (hblow : Tendsto (fun k => g k (z k)) atTop atTop) :
    ∃ ζ : ℕ → ℂ, ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧ Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun k => ε k * g k (ζ k)) atTop atTop ∧
      Tendsto (fun k => ‖z k - ζ k‖) atTop (𝓝 0) ∧ (∀ k, 0 < g k (ζ k)) ∧
      (∀ k, closedBall (ζ k) (ε k) ⊆ U k) ∧
      ∀ k, ∀ y ∈ closedBall (ζ k) (ε k), g k y ≤ 2 * g k (ζ k) := by
  set ε₀ : ℕ → ℝ := fun k => min (ρ / 3) (√(g k (z k)))⁻¹ with hε₀
  have hsq : ∀ k, 0 < √(g k (z k)) := fun k => Real.sqrt_pos.2 (hpos k)
  have hε₀pos : ∀ k, 0 < ε₀ k := fun k => lt_min (by linarith) (inv_pos.2 (hsq k))
  have hH : ∀ k, ∃ ζ : ℂ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ k ∧ ε₀ k * g k (z k) ≤ ε * g k ζ ∧
      ‖z k - ζ‖ ≤ 2 * ε₀ k ∧ closedBall ζ ε ⊆ U k ∧
      ∀ y ∈ closedBall ζ ε, g k y ≤ 2 * g k ζ := by
    intro k
    set X : Set ℂ := closedBall (z k) ρ with hX
    haveI : CompleteSpace X := isClosed_closedBall.isComplete.completeSpace_coe
    have hcont : Continuous (fun x : X => g k x) :=
      (hg k).comp_continuous continuous_subtype_val (fun x => hball k x.2)
    obtain ⟨x, ε, hε, hεle, hεg, hdist, hbd⟩ :=
      hofer_lemma (fun x : X => g k x) hcont (fun _ => hg0 _ _)
        ⟨z k, mem_closedBall_self hρ.le⟩ (ε₀ k) (hε₀pos k)
    have h3 : ε₀ k ≤ ρ / 3 := min_le_left _ _
    have hsubX : closedBall (x : ℂ) ε ⊆ X := by
      intro y hy
      rw [mem_closedBall] at hy
      rw [hX, mem_closedBall]
      have h1 : dist (x : ℂ) (z k) ≤ 2 * ε₀ k := hdist
      linarith [dist_triangle y x (z k)]
    refine ⟨x, ε, hε, hεle, hεg, ?_, hsubX.trans (hball k), fun y hy => hbd ⟨y, hsubX hy⟩ hy⟩
    have h1 : dist (x : ℂ) (z k) ≤ 2 * ε₀ k := hdist
    rwa [dist_eq_norm, norm_sub_rev] at h1
  choose ζ ε hε hεle hεg hdist hsub hbd using hH
  have hsqt : Tendsto (fun k => √(g k (z k))) atTop atTop := Real.tendsto_sqrt_atTop.comp hblow
  have hε₀0 : Tendsto ε₀ atTop (𝓝 0) := by
    have h := tendsto_inv_atTop_zero.comp hsqt
    refine squeeze_zero (fun k => (hε₀pos k).le) (fun k => min_le_right _ _) h
  have hlow : Tendsto (fun k => ε₀ k * g k (z k)) atTop atTop := by
    -- `ε₀ g = min (ρ g / 3) √g`
    have h1 : Tendsto (fun k => ρ / 3 * g k (z k)) atTop atTop :=
      hblow.const_mul_atTop (by linarith)
    have hmin : Tendsto (fun k => min (ρ / 3 * g k (z k)) √(g k (z k))) atTop atTop :=
      tendsto_atTop.2 fun b => ((h1.eventually_ge_atTop b).and (hsqt.eventually_ge_atTop b)).mono
        fun k hk => le_min hk.1 hk.2
    refine tendsto_atTop_mono (fun k => ?_) hmin
    have hgk := hpos k
    have hs := hsq k
    have hsg : (√(g k (z k)))⁻¹ * g k (z k) = √(g k (z k)) := by
      rw [inv_mul_eq_div, div_eq_iff hs.ne', Real.mul_self_sqrt (hg0 k (z k))]
    rcases le_total (ρ / 3) (√(g k (z k)))⁻¹ with h | h
    · rw [show ε₀ k = ρ / 3 from min_eq_left h]
      exact min_le_left _ _
    · rw [show ε₀ k = (√(g k (z k)))⁻¹ from min_eq_right h, hsg]
      exact min_le_right _ _
  refine ⟨ζ, ε, hε, squeeze_zero (fun k => (hε k).le) hεle hε₀0,
    tendsto_atTop_mono hεg hlow, ?_, fun k => ?_, hsub, hbd⟩
  · refine squeeze_zero (fun k => norm_nonneg _) hdist ?_
    simpa using hε₀0.const_mul 2
  · have h1 : 0 < ε k * g k (ζ k) :=
      lt_of_lt_of_le (mul_pos (hε₀pos k) (hpos k)) (hεg k)
    exact pos_of_mul_pos_right h1 (hε k).le

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (g : ℕ → ℂ → ℝ) (U : ℕ → Set ℂ) (z : ℕ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hball : ∀ k, closedBall (z k) ρ ⊆ U k) (hg : ∀ k, ContinuousOn (g k) (U k))
    (hg0 : ∀ k w, 0 ≤ g k w) (hpos : ∀ k, 0 < g k (z k))
    (hblow : Tendsto (fun k => g k (z k)) atTop atTop) :
    ∃ ζ : ℕ → ℂ, ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧ Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun k => ε k * g k (ζ k)) atTop atTop ∧
      Tendsto (fun k => ‖z k - ζ k‖) atTop (𝓝 0) ∧ (∀ k, 0 < g k (ζ k)) ∧
      (∀ k, closedBall (ζ k) (ε k) ⊆ U k) ∧
      ∀ k, ∀ y ∈ closedBall (ζ k) (ε k), g k y ≤ 2 * g k (ζ k) :=
  exists_blowup_points_aux g U z ρ hρ hball hg hg0 hpos hblow

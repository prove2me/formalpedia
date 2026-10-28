-- Prove2me | solution 2 for FiniteEnergyPlane.continuousOn_proj
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-25T23:44:16.276159+00:00
-- url     : https://prove2.me/submissions/832d4dac-b797-4aa8-b60d-82ed9d8904d4

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Definitions.Def_FiniteEnergyPlane_Setting

open FiniteEnergyPlane MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) :
    ContinuousOn (proj H) {0}ᶜ := by
  obtain ⟨hHs, huniq, htr⟩ := hH
  have hdiff : Differentiable ℝ H := hHs.differentiable (by simp)
  have hcont : Continuous H := hHs.continuous
  have hspec : ∀ y : V n, y ≠ 0 → 0 < scaleToS H y ∧ H (scaleToS H y • y) = 1 := by
    intro y hy
    have h : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := (huniq y hy).exists
    rw [scaleToS, dif_pos h]; exact Classical.choose_spec h
  have heq : ∀ y : V n, y ≠ 0 → ∀ r, 0 < r → H (r • y) = 1 → scaleToS H y = r :=
    fun y hy r hr hHr => (huniq y hy).unique (hspec y hy) ⟨hr, hHr⟩
  have hsc : ContinuousOn (scaleToS H) {0}ᶜ := by
    intro y₀ hy₀
    have hy₀' : y₀ ≠ 0 := hy₀
    obtain ⟨hr₀, hH₀⟩ := hspec y₀ hy₀'
    set r₀ := scaleToS H y₀ with hr₀def
    have hd : HasDerivAt (fun r : ℝ => H (r • y₀)) (fderiv ℝ H (r₀ • y₀) y₀) r₀ := by
      have := (hdiff (r₀ • y₀)).hasFDerivAt.comp_hasDerivAt r₀ ((hasDerivAt_id r₀).smul_const y₀)
      rw [one_smul] at this
      exact this
    have hpos : 0 < fderiv ℝ H (r₀ • y₀) y₀ := by
      have h1 := htr _ hH₀
      rw [map_smul, smul_eq_mul] at h1
      exact pos_of_mul_pos_right h1 hr₀.le
    have hslope := (hasDerivAt_iff_tendsto_slope.1 hd).eventually (lt_mem_nhds hpos)
    obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hslope)
    rw [ContinuousWithinAt, Metric.tendsto_nhds]
    intro ε hε
    set η := min (min ε ε₀) r₀ / 2 with hηdef
    have hm : 0 < min (min ε ε₀) r₀ := lt_min (lt_min hε hε₀) hr₀
    have hη : 0 < η := half_pos hm
    have hηε : η < ε := (half_lt_self hm).trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hηε₀ : η < ε₀ := (half_lt_self hm).trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hηr : η < r₀ := (half_lt_self hm).trans_le (min_le_right _ _)
    have hlo : H ((r₀ - η) • y₀) < 1 := by
      have hdist : dist (r₀ - η) r₀ < ε₀ := by
        rw [Real.dist_eq, show r₀ - η - r₀ = -η by ring, abs_neg, abs_of_pos hη]; exact hηε₀
      have := hball hdist (show r₀ - η ≠ r₀ by linarith)
      rw [slope_def_field, hH₀, show r₀ - η - r₀ = -η by ring, div_neg, neg_pos] at this
      have := mul_neg_of_neg_of_pos this hη
      rw [div_mul_cancel₀ _ hη.ne'] at this
      linarith
    have hhi : 1 < H ((r₀ + η) • y₀) := by
      have hdist : dist (r₀ + η) r₀ < ε₀ := by
        rw [Real.dist_eq, show r₀ + η - r₀ = η by ring, abs_of_pos hη]; exact hηε₀
      have := hball hdist (show r₀ + η ≠ r₀ by linarith)
      rw [slope_def_field, hH₀, show r₀ + η - r₀ = η by ring] at this
      have := mul_pos this hη
      rw [div_mul_cancel₀ _ hη.ne'] at this
      linarith
    have hc1 : Continuous fun y : V n => H ((r₀ - η) • y) := hcont.comp (continuous_const_smul _)
    have hc2 : Continuous fun y : V n => H ((r₀ + η) • y) := hcont.comp (continuous_const_smul _)
    filter_upwards [nhdsWithin_le_nhds (hc1.continuousAt.eventually (gt_mem_nhds hlo)),
      nhdsWithin_le_nhds (hc2.continuousAt.eventually (lt_mem_nhds hhi)), self_mem_nhdsWithin]
      with y h1 h2 hy
    have hcon : ContinuousOn (fun r : ℝ => H (r • y)) (Set.Icc (r₀ - η) (r₀ + η)) :=
      (hcont.comp (continuous_id.smul continuous_const)).continuousOn
    obtain ⟨r, hr, hHr⟩ := intermediate_value_Icc (by linarith) hcon ⟨h1.le, h2.le⟩
    rw [heq y hy r (by linarith [hr.1]) hHr, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  exact hsc.smul continuousOn_id

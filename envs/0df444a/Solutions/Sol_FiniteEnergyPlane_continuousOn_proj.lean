-- Prove2me | solution 1 for FiniteEnergyPlane.continuousOn_proj
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:21:04.069992+00:00
-- url     : https://prove2.me/submissions/ed867ea2-8b3e-4fcb-8f28-2898ed7b60ab

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Setting

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

namespace S177PJ
open FiniteEnergyPlane

variable {n : ℕ}

lemma spec {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n} (hy : y ≠ 0) :
    0 < scaleToS H y ∧ H (scaleToS H y • y) = 1 := by
  have hex : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := (hH.2.1 y hy).exists
  unfold scaleToS; rw [dif_pos hex]; exact Classical.choose_spec hex

lemma uniq {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n} (hy : y ≠ 0) {r : ℝ}
    (hr : 0 < r) (h1 : H (r • y) = 1) : r = scaleToS H y :=
  (hH.2.1 y hy).unique ⟨hr, h1⟩ (spec hH hy)

lemma contAt {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y₀ : V n} (hy₀ : y₀ ≠ 0) :
    ContinuousAt (scaleToS H) y₀ := by
  obtain ⟨hr0, hg0⟩ := spec hH hy₀
  set r₀ := scaleToS H y₀
  have hHd : Differentiable ℝ H := hH.1.differentiable (by simp)
  have hHc : Continuous H := hH.1.continuous
  set g : ℝ → ℝ := fun r => H (r • y₀)
  have hgd : HasDerivAt g (fderiv ℝ H (r₀ • y₀) y₀) r₀ := by
    have h1 : HasDerivAt (fun r : ℝ => r • y₀) y₀ r₀ := by
      simpa using (hasDerivAt_id r₀).smul_const y₀
    have := (hHd (r₀ • y₀)).hasFDerivAt.comp_hasDerivAt r₀ h1
    exact this
  have hpos : 0 < fderiv ℝ H (r₀ • y₀) y₀ := by
    have h := hH.2.2 _ hg0
    rw [map_smul, smul_eq_mul] at h
    exact pos_of_mul_pos_right h hr0.le
  have hsl := hasDerivAt_iff_tendsto_slope.1 hgd
  have hev : ∀ᶠ r in 𝓝[≠] r₀, 0 < slope g r₀ r := hsl.eventually (lt_mem_nhds hpos)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨η, hη, hη'⟩ := hev
  rw [Metric.continuousAt_iff]
  intro ε hε
  set δ := min (η / 2) (min (ε / 2) (r₀ / 2))
  have hδ : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hδη : δ < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδε : δ < ε := lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith)
  have hδr : δ < r₀ := lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)
  have slope_pos : ∀ r, r ≠ r₀ → |r - r₀| < η → 0 < (r - r₀)⁻¹ * (g r - 1) := by
    intro r hne hd
    have := hη' (by rw [Real.dist_eq]; exact hd) hne
    rw [slope_def_field] at this
    rw [inv_mul_eq_div, ← hg0]; exact this
  have glo : g (r₀ - δ) < 1 := by
    have := slope_pos (r₀ - δ) (by linarith) (by rw [abs_lt]; constructor <;> linarith)
    have hneg : (r₀ - δ - r₀)⁻¹ < 0 := inv_lt_zero.2 (by linarith)
    by_contra hc; push Not at hc
    have : (r₀ - δ - r₀)⁻¹ * (g (r₀ - δ) - 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg.le (by linarith)
    linarith
  have ghi : 1 < g (r₀ + δ) := by
    have := slope_pos (r₀ + δ) (by linarith) (by rw [abs_lt]; constructor <;> linarith)
    have hp : 0 < (r₀ + δ - r₀)⁻¹ := inv_pos.2 (by linarith)
    by_contra hc; push Not at hc
    have : (r₀ + δ - r₀)⁻¹ * (g (r₀ + δ) - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hp.le (by linarith)
    linarith
  have c1 : Continuous fun y : V n => H ((r₀ - δ) • y) := hHc.comp (continuous_const_smul _)
  have c2 : Continuous fun y : V n => H ((r₀ + δ) • y) := hHc.comp (continuous_const_smul _)
  have e1 : ∀ᶠ y in 𝓝 y₀, H ((r₀ - δ) • y) < 1 := c1.continuousAt.eventually (gt_mem_nhds glo)
  have e2 : ∀ᶠ y in 𝓝 y₀, 1 < H ((r₀ + δ) • y) := c2.continuousAt.eventually (lt_mem_nhds ghi)
  have e3 : ∀ᶠ y in 𝓝 y₀, y ≠ 0 := isOpen_ne.mem_nhds hy₀
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff.1 (e1.and (e2.and e3))
  refine ⟨ρ, hρ, fun {y} hy => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hρ' hy
  have hcont : ContinuousOn (fun r : ℝ => H (r • y)) (Set.Icc (r₀ - δ) (r₀ + δ)) :=
    (hHc.comp (continuous_id.smul continuous_const)).continuousOn
  obtain ⟨r, hr, hr1⟩ := intermediate_value_Icc (by linarith) hcont ⟨h1.le, h2.le⟩
  have := uniq hH h3 (by linarith [hr.1]) hr1
  rw [← this, Real.dist_eq, abs_lt]
  constructor <;> linarith [hr.1, hr.2]

end S177PJ

open FiniteEnergyPlane in
theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) :
    ContinuousOn (proj H) {0}ᶜ := by
  intro y hy
  exact ((S177PJ.contAt hH hy).smul continuousAt_id).continuousWithinAt

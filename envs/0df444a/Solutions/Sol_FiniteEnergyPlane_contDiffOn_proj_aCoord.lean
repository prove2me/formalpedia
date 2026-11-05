-- Prove2me | solution 1 for FiniteEnergyPlane.contDiffOn_proj_aCoord
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T19:51:21.702608+00:00
-- url     : https://prove2.me/submissions/4f3d170b-1ea1-4673-9046-3070eade73af

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.Log.Deriv



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- On a strictly star-shaped level `S = H⁻¹(1)`, the radial projection `proj H` and the
symplectization coordinate `aCoord H` are `C^∞` on `V n \ {0}`. -/
theorem contDiffOn_proj_aCoord {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) :
    ContDiffOn ℝ ∞ (proj H) {0}ᶜ ∧ ContDiffOn ℝ ∞ (aCoord H) {0}ᶜ := by
  have spec : ∀ y : V n, y ≠ 0 → 0 < scaleToS H y ∧ H (scaleToS H y • y) = 1 := by
    intro y hy
    have hex : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := (hH.2.1 y hy).exists
    unfold scaleToS
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  have uniq : ∀ y : V n, y ≠ 0 → ∀ r : ℝ, 0 < r → H (r • y) = 1 → scaleToS H y = r :=
    fun y hy r hr h1 => (hH.2.1 y hy).unique (spec y hy) ⟨hr, h1⟩
  have hsc : ContDiffOn ℝ ∞ (scaleToS H) {0}ᶜ := by
    intro y₀ hy₀
    refine ContDiffAt.contDiffWithinAt ?_
    obtain ⟨hr₀, h1⟩ := spec y₀ hy₀
    set r₀ := scaleToS H y₀
    set f : V n × ℝ → ℝ := fun p => H (p.2 • p.1) with hf
    have hHd : ContDiff ℝ ∞ H := hH.1
    have hfc : ContDiff ℝ ∞ f := hHd.comp (contDiff_snd.smul contDiff_fst)
    have cdf : ContDiffAt ℝ ∞ f (y₀, r₀) := hfc.contDiffAt
    set x := r₀ • y₀
    have hHx : HasFDerivAt H (fderiv ℝ H x) x :=
      (hHd.differentiable (by simp)).differentiableAt.hasFDerivAt
    have hg : HasFDerivAt (fun p : V n × ℝ => p.2 • p.1)
        (r₀ • ContinuousLinearMap.fst ℝ (V n) ℝ +
          (ContinuousLinearMap.snd ℝ (V n) ℝ).smulRight y₀) (y₀, r₀) := by
      have hs : HasFDerivAt (fun p : V n × ℝ => p.2) (ContinuousLinearMap.snd ℝ (V n) ℝ)
          (y₀, r₀) := hasFDerivAt_snd
      have hf1 : HasFDerivAt (fun p : V n × ℝ => p.1) (ContinuousLinearMap.fst ℝ (V n) ℝ)
          (y₀, r₀) := hasFDerivAt_fst
      simpa using hs.smul hf1
    have hfd : HasFDerivAt f ((fderiv ℝ H x).comp (r₀ • ContinuousLinearMap.fst ℝ (V n) ℝ +
          (ContinuousLinearMap.snd ℝ (V n) ℝ).smulRight y₀)) (y₀, r₀) := hHx.comp (y₀, r₀) hg
    have hpos : 0 < fderiv ℝ H x y₀ := by
      have h := hH.2.2 x h1
      have : fderiv ℝ H x x = r₀ * fderiv ℝ H x y₀ := by simp [x, map_smul]
      rw [this] at h
      exact pos_of_mul_pos_right h hr₀.le
    have hL : (fderiv ℝ f (y₀, r₀) ∘L .inr ℝ (V n) ℝ) =
        (fderiv ℝ H x y₀) • ContinuousLinearMap.id ℝ ℝ := by
      rw [hfd.fderiv]
      ext
      simp
    have if₂ : (fderiv ℝ f (y₀, r₀) ∘L .inr ℝ (V n) ℝ).IsInvertible := by
      rw [hL]
      exact ⟨ContinuousLinearEquiv.smulLeft (Units.mk0 _ hpos.ne'), by ext; simp⟩
    have pn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
    set ψ := cdf.implicitFunction pn if₂
    have hψ0 : ψ y₀ = r₀ := cdf.implicitFunction_apply_self pn if₂
    have hψc : ContDiffAt ℝ ∞ ψ y₀ := cdf.contDiffAt_implicitFunction pn if₂
    have hev := cdf.eventually_apply_implicitFunction pn if₂
    have hψpos : ∀ᶠ y in 𝓝 y₀, 0 < ψ y :=
      hψc.continuousAt.eventually (lt_mem_nhds (hψ0 ▸ hr₀))
    have hne : ∀ᶠ y in 𝓝 y₀, y ≠ 0 := isOpen_ne.mem_nhds hy₀
    refine hψc.congr_of_eventuallyEq ?_
    filter_upwards [hev, hψpos, hne] with y hy hp hy0
    apply uniq y hy0 _ hp
    have hy' : H (ψ y • y) = H (r₀ • y₀) := hy
    rw [hy']
    exact h1
  refine ⟨hsc.smul contDiffOn_id, ?_⟩
  have : ContDiffOn ℝ ∞ (fun y => Real.log (scaleToS H y)) {0}ᶜ :=
    hsc.log (fun y hy => (spec y hy).1.ne')
  exact (this.neg.div_const 2).congr (fun y _ => by simp [aCoord, neg_div])

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) :
    ContDiffOn ℝ ∞ (proj H) {0}ᶜ ∧ ContDiffOn ℝ ∞ (aCoord H) {0}ᶜ :=
  contDiffOn_proj_aCoord H hH

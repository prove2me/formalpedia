-- Prove2me | solution 1 for FiniteEnergyPlane.exists_holomorphic_eqOn_of_accPt_intersection
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-05T20:57:02.777548+00:00
-- url     : https://prove2.me/submissions/548829ea-0835-47f4-a346-1a37a49d2f3f

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_exists_normal_chart_norm_dbar_le
import Theorems.Thm_FiniteEnergyPlane_eventually_eq_zero_of_norm_dbar_le
import Theorems.Thm_FiniteEnergyPlane_differentiableAt_complex_of_eventuallyEq_comp

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

namespace FiniteEnergyPlane

theorem exists_holomorphic_eqOn_of_accPt_intersection_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (U W : Set ℂ) (hU : IsOpen U) (hW : IsOpen W) (u v : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J U u) (hv : IsFiniteEnergyCurve H J W v)
    (hui : ∀ z ∈ U, Function.Injective (fderiv ℝ u z))
    (hvi : ∀ w ∈ W, Function.Injective (fderiv ℝ v w))
    (z₀ w₀ : ℂ) (hz₀ : z₀ ∈ U) (hw₀ : w₀ ∈ W) (z w : ℕ → ℂ)
    (hz : Tendsto z atTop (𝓝 z₀)) (hw : Tendsto w atTop (𝓝 w₀))
    (hne : ∀ k, (z k, w k) ≠ (z₀, w₀)) (heq : ∀ k, u (z k) = v (w k)) :
    ∃ ε > 0, ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (ball z₀ ε) ∧ φ z₀ = w₀ ∧ deriv φ z₀ ≠ 0 ∧
      Set.MapsTo φ (ball z₀ ε) W ∧ Set.EqOn u (v ∘ φ) (ball z₀ ε) := by
  have hE : Module.finrank ℝ (V 1) = 4 := by simp
  obtain ⟨hJt, -, -, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have huat : ∀ z ∈ U, ContDiffAt ℝ ∞ u z := fun z hz => hu.1.contDiffAt (hU.mem_nhds hz)
  have hvat : ∀ w ∈ W, ContDiffAt ℝ ∞ v w := fun w hw => hv.1.contDiffAt (hW.mem_nhds hw)
  have h₀ : u z₀ = v w₀ := by
    have h1 : Tendsto (fun k => u (z k)) atTop (𝓝 (u z₀)) :=
      (huat z₀ hz₀).continuousAt.tendsto.comp hz
    have h2 : Tendsto (fun k => v (w k)) atTop (𝓝 (v w₀)) :=
      (hvat w₀ hw₀).continuousAt.tendsto.comp hw
    simp only [heq] at h1
    exact tendsto_nhds_unique h1 h2
  obtain ⟨Ψ, Ξ, R, M, hR, hΨax, hLI, hΞ0, hcd, hbd⟩ :=
    exists_normal_chart_norm_dbar_le hE (Jtilde H J) {y | y ≠ 0} hJt U W hU hW u v hu.1 hv.1
      hu.2.1 hv.2.1 hu.2.2.1 hv.2.2.1 z₀ w₀ hz₀ hw₀ h₀ (hvi w₀ hw₀)
  have hz₀R : z₀ ∈ ball z₀ R := mem_ball_self hR
  -- the intersection points are zeros of the normal component
  have hwp : Tendsto (fun k => ((w k - w₀, (0 : ℂ)) : ℂ × ℂ)) atTop (𝓝 ((0 : ℂ), (0 : ℂ))) := by
    refine Tendsto.prodMk_nhds ?_ tendsto_const_nhds
    simpa using hw.sub_const w₀
  have hval : ∀ᶠ k in atTop, Ξ (u (z k)) = (w k - w₀, 0) := by
    filter_upwards [hwp.eventually hLI] with k hk
    have h1 : Ψ (w k - w₀, 0) = u (z k) := by
      rw [hΨax, add_sub_cancel, heq]
    rwa [h1] at hk
  have hzne : ∀ᶠ k in atTop, z k ≠ z₀ := by
    filter_upwards [hval] with k hk hzk
    rw [hzk, hΞ0] at hk
    have hk1 : w k - w₀ = 0 := (congrArg Prod.fst hk).symm
    exact hne k (by rw [hzk, sub_eq_zero.1 hk1])
  have hzw : Tendsto z atTop (𝓝[≠] z₀) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hz hzne
  have hacc : ∃ᶠ y in 𝓝[≠] z₀, (Ξ (u y)).2 = 0 := by
    refine hzw.frequently (Eventually.frequently ?_)
    filter_upwards [hval] with k hk
    rw [hk]
  have hg : ContDiffOn ℝ ∞ (fun y => (Ξ (u y)).2) (ball z₀ R) :=
    contDiff_snd.comp_contDiffOn hcd
  have hg0 := eventually_eq_zero_of_norm_dbar_le (fun y => (Ξ (u y)).2) (ball z₀ R) isOpen_ball hg M
    (fun y hy => (hbd y hy).2.2.2) z₀ hz₀R hacc
  obtain ⟨ε₁, hε₁, hε₁s⟩ := Metric.eventually_nhds_iff_ball.1 hg0
  set ε := min ε₁ R with hεdef
  have hε : 0 < ε := lt_min hε₁ hR
  have hsub1 : ball z₀ ε ⊆ ball z₀ ε₁ := ball_subset_ball (min_le_left _ _)
  have hsubR : ball z₀ ε ⊆ ball z₀ R := ball_subset_ball (min_le_right _ _)
  set φ : ℂ → ℂ := fun y => w₀ + (Ξ (u y)).1 with hφdef
  have hrep : ∀ y ∈ ball z₀ ε, u y = v (φ y) := by
    intro y hy
    have h1 := (hbd y (hsubR hy)).2.1
    have h2 : Ξ (u y) = ((Ξ (u y)).1, 0) := by
      ext1
      · rfl
      · exact hε₁s y (hsub1 hy)
    rw [h2, hΨax] at h1
    exact h1.symm
  have hφW : Set.MapsTo φ (ball z₀ ε) W := fun y hy => (hbd y (hsubR hy)).2.2.1
  have hφs : ContDiffOn ℝ ∞ φ (ball z₀ R) :=
    contDiffOn_const.add (contDiff_fst.comp_contDiffOn hcd)
  have hφr : ∀ y ∈ ball z₀ ε, DifferentiableAt ℝ φ y := fun y hy =>
    (hφs.contDiffAt (isOpen_ball.mem_nhds (hsubR hy))).differentiableAt (by simp)
  have hEv : ∀ y ∈ ball z₀ ε, u =ᶠ[𝓝 y] v ∘ φ := fun y hy =>
    Filter.mem_of_superset (isOpen_ball.mem_nhds hy) fun x hx => hrep x hx
  have hφC : ∀ y ∈ ball z₀ ε, DifferentiableAt ℂ φ y := by
    intro y hy
    have hyU : y ∈ U := (hbd y (hsubR hy)).1
    have hyW := hφW hy
    exact differentiableAt_complex_of_eventuallyEq_comp (Jtilde H J) u v φ y
      (hJt.2.2 _ (hu.2.1 y hyU)) (hφr y hy) ((hvat _ hyW).differentiableAt (by simp)) (hEv y hy)
      (hu.2.2.1 y hyU).2 (hv.2.2.1 _ hyW).2 (hvi _ hyW)
  have hz₀ε : z₀ ∈ ball z₀ ε := mem_ball_self hε
  have hφ0 : φ z₀ = w₀ := by
    simp only [hφdef]
    rw [hΞ0]
    simp
  refine ⟨ε, hε, φ, fun y hy => (hφC y hy).differentiableWithinAt, hφ0, ?_, hφW, hrep⟩
  intro hder
  have hv0 : DifferentiableAt ℝ v (φ z₀) := (hvat _ (hφW hz₀ε)).differentiableAt (by simp)
  have hdu : fderiv ℝ u z₀ = (fderiv ℝ v (φ z₀)).comp (fderiv ℝ φ z₀) := by
    rw [(hEv z₀ hz₀ε).fderiv_eq]
    exact (hv0.hasFDerivAt.comp z₀ (hφr z₀ hz₀ε).hasFDerivAt).fderiv
  have hL1 : fderiv ℝ φ z₀ 1 = 0 := by
    have h1 : HasFDerivAt φ ((fderiv ℂ φ z₀).restrictScalars ℝ) z₀ :=
      (hφC z₀ hz₀ε).hasFDerivAt.restrictScalars ℝ
    rw [h1.fderiv]
    exact hder
  have hu0 : fderiv ℝ u z₀ 1 = 0 := by
    rw [hdu, ContinuousLinearMap.comp_apply, hL1, map_zero]
  have := hui z₀ hz₀ (a₁ := 1) (a₂ := 0) (by rw [hu0, map_zero])
  exact one_ne_zero this

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (U W : Set ℂ) (hU : IsOpen U) (hW : IsOpen W) (u v : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J U u) (hv : IsFiniteEnergyCurve H J W v)
    (hui : ∀ z ∈ U, Function.Injective (fderiv ℝ u z))
    (hvi : ∀ w ∈ W, Function.Injective (fderiv ℝ v w))
    (z₀ w₀ : ℂ) (hz₀ : z₀ ∈ U) (hw₀ : w₀ ∈ W) (z w : ℕ → ℂ)
    (hz : Tendsto z atTop (𝓝 z₀)) (hw : Tendsto w atTop (𝓝 w₀))
    (hne : ∀ k, (z k, w k) ≠ (z₀, w₀)) (heq : ∀ k, u (z k) = v (w k)) :
    ∃ ε > 0, ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (ball z₀ ε) ∧ φ z₀ = w₀ ∧ deriv φ z₀ ≠ 0 ∧
      Set.MapsTo φ (ball z₀ ε) W ∧ Set.EqOn u (v ∘ φ) (ball z₀ ε) :=
  exists_holomorphic_eqOn_of_accPt_intersection_aux H hH J hJ U W hU hW u v hu hv hui hvi z₀ w₀ hz₀ hw₀ z w hz hw hne heq

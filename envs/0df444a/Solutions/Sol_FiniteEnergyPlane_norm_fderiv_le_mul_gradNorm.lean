-- Prove2me | solution 1 for FiniteEnergyPlane.norm_fderiv_le_mul_gradNorm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-25T18:24:12.909683+00:00
-- url     : https://prove2.me/submissions/ba571533-bc9b-41f3-b0c9-9accc9c891ab

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.MetricSpace.ProperSpace



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- On a slab the Euclidean derivative is bounded by the `ℝ`-invariant gradient norm. -/
theorem norm_fderiv_le_mul_gradNorm_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (A : ℝ) :
    ∃ M : ℝ, ∀ (u : ℂ → V n) (z : ℂ), DifferentiableAt ℝ u z → u z ≠ 0 →
      |aCoord H (u z)| ≤ A → ‖fderiv ℝ u z‖ ≤ M * gradNorm H u z := by
  obtain ⟨-, hprojs, haCs, hrep, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hOo : IsOpen {y : V n | y ≠ 0} := isOpen_ne
  -- `proj` is scale invariant
  have hproj : ∀ y : V n, y ≠ 0 → ∀ c : ℝ, 0 < c → proj H (c • y) = proj H y := by
    intro y hy c hc
    obtain ⟨r, ⟨hr0, hr1⟩, hru⟩ := hH.2.1 y hy
    have e1 : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := ⟨r, hr0, hr1⟩
    have e2 : ∃ r : ℝ, 0 < r ∧ H (r • (c • y)) = 1 :=
      ⟨r / c, div_pos hr0 hc, by rw [smul_smul, div_mul_cancel₀ _ hc.ne']; exact hr1⟩
    have h1 : scaleToS H y = r := by
      unfold scaleToS
      rw [dif_pos e1]
      exact hru _ (Classical.choose_spec e1)
    have h2 : scaleToS H (c • y) = r / c := by
      unfold scaleToS
      rw [dif_pos e2]
      have hs2 := Classical.choose_spec e2
      have := hru (Classical.choose e2 * c) ⟨mul_pos hs2.1 hc, by rw [← smul_smul]; exact hs2.2⟩
      rw [← this, mul_div_cancel_right₀ _ hc.ne']
    unfold proj
    rw [h1, h2, smul_smul, div_mul_cancel₀ _ hc.ne']
  -- `proj` is bounded
  have hsph : ∀ y ∈ sphere (0 : V n) 1, y ≠ 0 := fun y hy =>
    ne_zero_of_mem_sphere one_ne_zero ⟨y, hy⟩
  obtain ⟨P₀, hP₀⟩ := isBounded_iff_forall_norm_le.1
    ((isCompact_sphere (0 : V n) 1).image_of_continuousOn
      (hprojs.continuousOn.mono fun y hy => hsph y hy)).isBounded
  set P := max P₀ 0 with hP
  have hPb : ∀ y : V n, y ≠ 0 → ‖proj H y‖ ≤ P := by
    intro y hy
    have hny : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hm : ‖y‖⁻¹ • y ∈ sphere (0 : V n) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hny.ne']
    rw [← hproj y hy _ (inv_pos.2 hny)]
    exact (hP₀ _ ⟨_, hm, rfl⟩).trans (le_max_left _ _)
  refine ⟨Real.exp (2 * A) * (2 * P + 1), fun u z hu hne ha => ?_⟩
  set α : ℂ → ℝ := fun w => aCoord H (u w) with hα
  set p : ℂ → V n := fun w => proj H (u w) with hp
  have hαd : HasFDerivAt α (fderiv ℝ α z) z :=
    (((haCs.differentiableOn (by simp) _ hne).differentiableAt
      (hOo.mem_nhds hne)).comp z hu).hasFDerivAt
  have hpd : HasFDerivAt p (fderiv ℝ p z) z :=
    (((hprojs.differentiableOn (by simp) _ hne).differentiableAt
      (hOo.mem_nhds hne)).comp z hu).hasFDerivAt
  have hev : u =ᶠ[𝓝 z] fun w => Real.exp (2 * α w) • p w := by
    filter_upwards [hu.continuousAt.preimage_mem_nhds (hOo.mem_nhds hne)] with w hw
    exact (hrep _ hw).2
  have hD := ((hαd.const_mul 2).exp).smul hpd
  rw [(hD.congr_of_eventuallyEq hev).fderiv]
  set e := Real.exp (2 * α z) with he
  have he0 : 0 < e := Real.exp_pos _
  have heA : e ≤ Real.exp (2 * A) := Real.exp_le_exp.2 (by
    have := (abs_le.1 ha).2
    simp only [hα]
    linarith)
  have hpz : ‖p z‖ ≤ P := hPb _ hne
  have hP0 : 0 ≤ P := le_max_right _ _
  have hg : gradNorm H u z = ‖fderiv ℝ α z‖ + ‖fderiv ℝ p z‖ := rfl
  rw [hg]
  have h1 : ‖e • fderiv ℝ p z‖ = e * ‖fderiv ℝ p z‖ := by
    rw [norm_smul, Real.norm_of_nonneg he0.le]
  have h2 : ‖(e • (2 : ℝ) • fderiv ℝ α z).smulRight (p z)‖ ≤ e * (2 * ‖fderiv ℝ α z‖) * P := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, norm_smul,
      Real.norm_of_nonneg he0.le, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hpz (by positivity)
  have hA0 := norm_nonneg (fderiv ℝ α z)
  have hp0 := norm_nonneg (fderiv ℝ p z)
  calc ‖e • fderiv ℝ p z + (e • (2 : ℝ) • fderiv ℝ α z).smulRight (p z)‖
      ≤ e * ‖fderiv ℝ p z‖ + e * (2 * ‖fderiv ℝ α z‖) * P := by
        rw [← h1]; exact (norm_add_le _ _).trans (add_le_add le_rfl h2)
    _ ≤ e * ((2 * P + 1) * (‖fderiv ℝ α z‖ + ‖fderiv ℝ p z‖)) := by
        nlinarith [mul_nonneg he0.le (mul_nonneg hP0 hp0), mul_nonneg he0.le hA0]
    _ ≤ Real.exp (2 * A) * ((2 * P + 1) * (‖fderiv ℝ α z‖ + ‖fderiv ℝ p z‖)) :=
        mul_le_mul_of_nonneg_right heA (by positivity)
    _ = _ := by ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (A : ℝ) :
    ∃ M : ℝ, ∀ (u : ℂ → V n) (z : ℂ), DifferentiableAt ℝ u z → u z ≠ 0 →
      |aCoord H (u z)| ≤ A → ‖fderiv ℝ u z‖ ≤ M * gradNorm H u z :=
  norm_fderiv_le_mul_gradNorm_aux H hH J hJ A

-- Prove2me | solution 1 for FiniteEnergyPlane.isCompact_aCoord_slab
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-25T18:21:35.527986+00:00
-- url     : https://prove2.me/submissions/dc88f46c-82be-4062-9405-64dedeb91e85

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.MetricSpace.ProperSpace



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Slabs of the symplectization are compact. -/
theorem isCompact_aCoord_slab_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (A : ℝ) :
    IsCompact {y : V n | y ≠ 0 ∧ |aCoord H y| ≤ A} := by
  obtain ⟨-, hprojs, -, hrep, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  -- scaling identities
  have hsc : ∀ y : V n, y ≠ 0 → ∀ c : ℝ, 0 < c →
      scaleToS H (c • y) = scaleToS H y / c ∧ 0 < scaleToS H y := by
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
    rw [h1, h2]
    exact ⟨rfl, hr0⟩
  have hproj : ∀ y : V n, y ≠ 0 → ∀ c : ℝ, 0 < c → proj H (c • y) = proj H y := by
    intro y hy c hc
    obtain ⟨h1, -⟩ := hsc y hy c hc
    unfold proj
    rw [h1, smul_smul, div_mul_cancel₀ _ hc.ne']
  have haC : ∀ y : V n, y ≠ 0 → ∀ c : ℝ, 0 < c →
      aCoord H (c • y) = aCoord H y + Real.log c / 2 := by
    intro y hy c hc
    obtain ⟨h1, h2⟩ := hsc y hy c hc
    unfold aCoord
    rw [h1, Real.log_div h2.ne' hc.ne']
    ring
  have hprojne : ∀ y : V n, y ≠ 0 → proj H y ≠ 0 ∧ aCoord H (proj H y) = 0 := by
    intro y hy
    obtain ⟨-, hs⟩ := hsc y hy 1 one_pos
    have hp : proj H y = scaleToS H y • y := rfl
    refine ⟨by rw [hp]; exact smul_ne_zero hs.ne' hy, ?_⟩
    rw [hp, haC y hy _ hs]
    unfold aCoord
    ring
  -- the slab is the image of `[-A, A] × sphere`
  set D : Set (ℝ × V n) := Set.Icc (-A) A ×ˢ sphere (0 : V n) 1 with hD
  have hDc : IsCompact D := isCompact_Icc.prod (isCompact_sphere 0 1)
  set f : ℝ × V n → V n := fun p => Real.exp (2 * p.1) • proj H p.2 with hf
  have hsph : ∀ y ∈ sphere (0 : V n) 1, y ≠ 0 := fun y hy => ne_zero_of_mem_sphere one_ne_zero ⟨y, hy⟩
  have hfc : ContinuousOn f D := by
    refine ContinuousOn.smul (f := fun p : ℝ × V n => Real.exp (2 * p.1))
      (g := fun p : ℝ × V n => proj H p.2) ?_ ?_
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).continuousOn
    · exact hprojs.continuousOn.comp continuous_snd.continuousOn
        (fun p hp => hsph p.2 hp.2)
  convert hDc.image_of_continuousOn hfc using 1
  ext y
  constructor
  · rintro ⟨hy, ha⟩
    have hny : 0 < ‖y‖ := norm_pos_iff.2 hy
    refine ⟨(aCoord H y, ‖y‖⁻¹ • y), ⟨abs_le.1 ha, ?_⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hny.ne']
    · simp only [hf]
      rw [hproj y hy _ (inv_pos.2 hny)]
      exact ((hrep y hy).2).symm
  · rintro ⟨⟨a, x⟩, ⟨ha, hx⟩, rfl⟩
    have hx0 := hsph x hx
    obtain ⟨hp0, hpa⟩ := hprojne x hx0
    refine ⟨smul_ne_zero (Real.exp_pos _).ne' hp0, ?_⟩
    simp only [hf]
    rw [haC _ hp0 _ (Real.exp_pos _), hpa, Real.log_exp, zero_add,
      show 2 * a / 2 = a by ring]
    exact abs_le.2 ha

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (A : ℝ) :
    IsCompact {y : V n | y ≠ 0 ∧ |aCoord H y| ≤ A} :=
  isCompact_aCoord_slab_aux H hH J hJ A

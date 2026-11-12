-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18i_zero_cutoff_square_law_of_equal_triplet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:47:11.347196+00:00
-- url     : https://prove2.me/submissions/e4a8766f-dc61-431d-b008-f46a142e8526

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_generic_negative_mark_window_integral_formula
import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_triplet
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original residual has a common explicit Borel path functional,
which transports its quadratic law between arbitrary universes. -/
theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν)
    (t : ℝ≥0) :
    P₁.map (fun ω : Ω₁ => (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ^ 2) =
      P₂.map (fun ω : Ω₂ => (avram_p4_h_gaussian_intrinsic_truncated_residual Y 0 t ω) ^ 2) := by
  classical
  let B : Set ℝ := Iic (-1 : ℝ)
  let g : ℝ → ℝ≥0∞ := fun z => if z ∈ B then ENNReal.ofReal (-z) else 0
  have hg : Measurable g := by
    dsimp [g]
    exact Measurable.ite measurableSet_Iic (by fun_prop) measurable_const
  obtain ⟨J, hJ, hJpath⟩ :=
    avram_bv_jump8_cadlag_mark_weight_lintegral_borel t g hg
  let W : (ℝ≥0 → ℝ) → ℝ := fun path =>
    path t - (t : ℝ) * X.c + (J path).toReal
  let Q : (ℝ≥0 → ℝ) → ℝ := fun path => (W path) ^ 2
  have hW : Measurable W :=
    ((measurable_pi_apply t).sub_const ((t : ℝ) * X.c)).add
      (ENNReal.measurable_toReal.comp hJ)
  have hQ : Measurable Q := hW.pow_const 2
  have hNeg : ∀ z ∈ B, z ≤ 0 := by
    intro z hz
    exact hz.trans (by norm_num)
  have hRX (ω : Ω₁) :
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
        W (fun u : ℝ≥0 => X.X u ω) := by
    let path : ℝ≥0 → ℝ := fun u => X.X u ω
    let μ : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ path u - Function.leftLim path u ≠ 0}).map
        (fun u : ℝ≥0 => (u, path u - Function.leftLim path u))
    have hJformula := hJpath path (X.rightCont ω) (X.leftLim ω)
    have hSign := avram_mix_gauss14_generic_negative_mark_window_integral_formula
      μ (0 : ℝ≥0) t B measurableSet_Iic hNeg
    have hLarge : avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω =
        -((J path).toReal) := by
      change (∫ p in (Ioc 0 t ×ˢ B), p.2 ∂μ) = -((J path).toReal)
      rw [hSign, hJformula]
    have hSmall : avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω = 0 := by
      simp [avram_p4_h_gaussian_intrinsic_small_band_compensated]
    change X.X t ω - (t : ℝ) * X.c -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω -
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω =
        path t - (t : ℝ) * X.c + (J path).toReal
    rw [hSmall, hLarge] <;> ring
  have hRY (ω : Ω₂) :
      avram_p4_h_gaussian_intrinsic_truncated_residual Y 0 t ω =
        W (fun u : ℝ≥0 => Y.X u ω) := by
    let path : ℝ≥0 → ℝ := fun u => Y.X u ω
    let μ : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ path u - Function.leftLim path u ≠ 0}).map
        (fun u : ℝ≥0 => (u, path u - Function.leftLim path u))
    have hJformula := hJpath path (Y.rightCont ω) (Y.leftLim ω)
    have hSign := avram_mix_gauss14_generic_negative_mark_window_integral_formula
      μ (0 : ℝ≥0) t B measurableSet_Iic hNeg
    have hLarge : avram_p4_h_gaussian_intrinsic_large_jump_sum Y t ω =
        -((J path).toReal) := by
      change (∫ p in (Ioc 0 t ×ˢ B), p.2 ∂μ) = -((J path).toReal)
      rw [hSign, hJformula]
    have hSmall : avram_p4_h_gaussian_intrinsic_small_band_compensated Y 0 t ω = 0 := by
      simp [avram_p4_h_gaussian_intrinsic_small_band_compensated]
    change Y.X t ω - (t : ℝ) * Y.c -
        avram_p4_h_gaussian_intrinsic_small_band_compensated Y 0 t ω -
        avram_p4_h_gaussian_intrinsic_large_jump_sum Y t ω =
        path t - (t : ℝ) * X.c + (J path).toReal
    rw [hSmall, hLarge, hc] <;> ring
  have hXmeas : Measurable (fun ω : Ω₁ => fun u : ℝ≥0 => X.X u ω) :=
    measurable_pi_iff.mpr (fun u => X.adapted.measurable)
  have hYmeas : Measurable (fun ω : Ω₂ => fun u : ℝ≥0 => Y.X u ω) :=
    measurable_pi_iff.mpr (fun u => Y.adapted.measurable)
  have hFX : (fun ω : Ω₁ =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ^ 2) =
      (fun ω : Ω₁ => Q (fun u : ℝ≥0 => X.X u ω)) := by
    funext ω
    exact congrArg (fun z : ℝ => z ^ 2) (hRX ω)
  have hFY : (fun ω : Ω₂ =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual Y 0 t ω) ^ 2) =
      (fun ω : Ω₂ => Q (fun u : ℝ≥0 => Y.X u ω)) := by
    funext ω
    exact congrArg (fun z : ℝ => z ^ 2) (hRY ω)
  rw [hFX, hFY]
  calc
    P₁.map (fun ω : Ω₁ => Q (fun u : ℝ≥0 => X.X u ω)) =
      (P₁.map (fun ω : Ω₁ => fun u : ℝ≥0 => X.X u ω)).map Q := by
        rw [Measure.map_map hQ hXmeas] <;> rfl
    _ = (P₂.map (fun ω : Ω₂ => fun u : ℝ≥0 => Y.X u ω)).map Q := by
      rw [cross_levy_whole_path_law_of_equal_triplet X Y hc hσ hν]
    _ = P₂.map (fun ω : Ω₂ => Q (fun u : ℝ≥0 => Y.X u ω)) := by
      rw [Measure.map_map hQ hYmeas] <;> rfl

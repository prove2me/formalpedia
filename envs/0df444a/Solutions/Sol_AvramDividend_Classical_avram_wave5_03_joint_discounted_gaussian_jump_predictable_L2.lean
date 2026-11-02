-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_joint_discounted_gaussian_jump_predictable_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:38:18.227966+00:00
-- url     : https://prove2.me/submissions/18b5eca5-9add-485a-8630-9226eceec016

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_controlled_gradient_predictable_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Joint same-clock original Gaussian and negative-jump integrand square energy, without assuming a stochastic integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw1 : ContDiffOn ℝ 1 w (Ioo a b))
    (hw2 : ContDiffOn ℝ 2 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) *
        (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
      else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => if Y p ∈ Icc u v then deriv w (Y p) else 0
    let J : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if Y p.1 ∈ Icc (u + δ) v then w (Y p.1 + p.2) - w (Y p.1) else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => ρ p.1 * J p
    @MemLp (ℝ≥0 × Ω) ℝ (𝓕.rightCont.predictable) _ _
      (fun p => ρ p * (X.σ * G p)) 2 μ ∧
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by
  dsimp only
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let ρ : ℝ≥0 × Ω → ℝ := fun p =>
    if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) *
      (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
    else 0
  let G : ℝ≥0 × Ω → ℝ := fun p => if Y p ∈ Icc u v then deriv w (Y p) else 0
  let J : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    if Y p.1 ∈ Icc (u + δ) v then w (Y p.1 + p.2) - w (Y p.1) else 0
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => ρ p.1 * J p
  change @MemLp (ℝ≥0 × Ω) ℝ (𝓕.rightCont.predictable) _ _
      (fun p => ρ p * (X.σ * G p)) 2 μ ∧
    Measurable[(𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)] H ∧
    (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤
  have hder (r : ℝ) : deriv (fun y : ℝ => y) r = 1 := (hasDerivAt_id r).deriv
  have hρsp : IsStronglyPredictable 𝓕.rightCont
      (fun t ω =>
        if t ≤ T then
          Real.exp (-(q * (t : ℝ))) *
            (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then
              (1 : ℝ) else 0)
        else 0) := by
    simpa only [hder, mul_one] using
      (avram_wave3_04_source_stopped_discounted_deriv_predictable
        X x D hD (fun y : ℝ => y) q T)
  change StronglyMeasurable[𝓕.rightCont.predictable] ρ at hρsp
  have hρm : Measurable[𝓕.rightCont.predictable] ρ :=
    hρsp.measurable
  have hρbound (p : ℝ≥0 × Ω) : |ρ p| ≤ 1 := by
    by_cases ht : p.1 ≤ T
    · by_cases hs : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2
      · have ht0 : (0 : ℝ) ≤ (p.1 : ℝ) := NNReal.coe_nonneg _
        have hqtime : 0 ≤ q * (p.1 : ℝ) := mul_nonneg hq ht0
        have he : Real.exp (-(q * (p.1 : ℝ))) ≤ 1 := by
          calc
            Real.exp (-(q * (p.1 : ℝ))) ≤ Real.exp 0 :=
              Real.exp_le_exp.mpr (by linarith)
            _ = 1 := Real.exp_zero
        simpa [ρ, ht, hs, abs_of_pos (Real.exp_pos _)] using he
      · simp [ρ, ht, hs]
    · simp [ρ, ht]
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)
  have henergy :=
    avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
      X x D hD w a b u v hw2 hau huv hvb μ hμ
  have hGmeas : Measurable G := henergy.1
  have hG : MemLp G 2 μ :=
    avram_wave4_04b_original_controlled_gradient_predictable_MemLp_two
      X x D hD w a b u v hw2 hau huv hvb μ hμ
  have hσ : MemLp (fun p => X.σ * G p) 2 μ := hG.const_mul X.σ
  have hprod : Measurable (fun p => ρ p * (X.σ * G p)) :=
    hρm.mul (measurable_const.mul hGmeas)
  have hdom : ∀ p : ℝ≥0 × Ω,
      ‖ρ p * (X.σ * G p)‖ ≤ ‖X.σ * G p‖ := by
    intro p
    simpa only [Real.norm_eq_abs, abs_mul, one_mul] using
      (mul_le_mul_of_nonneg_right (hρbound p) (abs_nonneg (X.σ * G p)))
  have hGaussian :
      @MemLp (ℝ≥0 × Ω) ℝ (𝓕.rightCont.predictable) _ _
        (fun p => ρ p * (X.σ * G p)) 2 μ := by
    exact hσ.of_le hprod.aestronglyMeasurable
      (Filter.Eventually.of_forall hdom)
  have hJ :=
    avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite
      X x D hD w a b u v δ hw1 hw_cont hw_neg
      hau huv hvb hu0 hδ hδone hband μ hμ
  have hJmeas : Measurable J := hJ.1
  have hJenergy :
      (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((J (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ := hJ.2
  have hρmark : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) => ρ p.1) :=
    hρm.comp measurable_fst
  have hHmeas : Measurable H := hρmark.mul hJmeas
  have hpoint (p : ((ℝ≥0 × Ω) × ℝ)) : (H p) ^ 2 ≤ (J p) ^ 2 := by
    have hb : -1 ≤ ρ p.1 ∧ ρ p.1 ≤ 1 := abs_le.mp (hρbound p.1)
    have hp : 0 ≤ 1 + ρ p.1 := by linarith
    have hm : 0 ≤ 1 - ρ p.1 := by linarith
    have hs : (ρ p.1) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hp hm]
    calc
      (H p) ^ 2 = (ρ p.1) ^ 2 * (J p) ^ 2 := by
        dsimp [H]
        ring
      _ ≤ 1 * (J p) ^ 2 :=
        mul_le_mul_of_nonneg_right hs (sq_nonneg (J p))
      _ = (J p) ^ 2 := one_mul _
  have hHenergy :
      (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by
    refine lt_of_le_of_lt ?_ hJenergy
    apply lintegral_mono
    intro p
    apply lintegral_mono
    intro z
    exact ENNReal.ofReal_le_ofReal (hpoint (p, z))
  exact ⟨hGaussian, hHmeas, hHenergy⟩

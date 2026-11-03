-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_bounded_predictable_discount_thinned_taylor_L1_L2_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:59:40.559046+00:00
-- url     : https://prove2.me/submissions/aef59459-d9c4-4afa-8bc0-63a8aff3cd14

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_stopped_C2_joint_predictable_thinning_finite_energy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Any bounded predictable discount keeps the thinned original stopped
Taylor correction measurable and with finite negative Lévy L1/L2 energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hS : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] S)
    (a : ℝ≥0 × Ω → ℝ)
    (ham : Measurable[𝓕.rightCont.predictable] a)
    (ha : ∀ p, 0 ≤ a p ∧ a p ≤ 1) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : ((ℝ≥0 × Ω) × ℝ) => a p.1 * (S.indicator HS) p) ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal (|a p * (S.indicator HS) (p,z)|) ∂X.ν ∂μ) < ⊤ ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((a p * (S.indicator HS) (p,z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by
  classical
  intro Y H HS
  have hBase :=
    avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv μ hμ
  have hEnergy :=
    avram_wave7_07_original_stopped_C2_joint_predictable_thinning_finite_energy
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv μ hμ S hS
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)
  have hWeightedMeas : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      a p.1 * (S.indicator HS) p) :=
    (ham.comp measurable_fst).mul (hBase.1.indicator hS)
  have hAbsBound (p : ℝ≥0 × Ω) (z : ℝ) :
      ENNReal.ofReal (|a p * (S.indicator HS) (p,z)|) ≤
        ENNReal.ofReal (|(S.indicator HS) (p,z)|) := by
    apply ENNReal.ofReal_le_ofReal
    rw [abs_mul, abs_of_nonneg (ha p).1]
    nlinarith [mul_nonneg (sub_nonneg.mpr (ha p).2)
      (abs_nonneg ((S.indicator HS) (p,z)))]
  have hSqBound (p : ℝ≥0 × Ω) (z : ℝ) :
      ENNReal.ofReal ((a p * (S.indicator HS) (p,z)) ^ 2) ≤
        ENNReal.ofReal (((S.indicator HS) (p,z)) ^ 2) := by
    apply ENNReal.ofReal_le_ofReal
    have haSq : (a p) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (ha p).2)
        (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) (ha p).1)]
    calc
      (a p * (S.indicator HS) (p,z)) ^ 2 =
          (a p) ^ 2 * ((S.indicator HS) (p,z)) ^ 2 := by ring
      _ ≤ 1 * ((S.indicator HS) (p,z)) ^ 2 :=
        mul_le_mul_of_nonneg_right haSq (sq_nonneg _)
      _ = ((S.indicator HS) (p,z)) ^ 2 := one_mul _
  refine ⟨hWeightedMeas, ?_, ?_⟩
  · apply lt_of_le_of_lt _ hEnergy.2.1
    apply lintegral_mono
    intro p
    apply lintegral_mono
    intro z
    exact hAbsBound p z
  · apply lt_of_le_of_lt _ hEnergy.2.2
    apply lintegral_mono
    intro p
    apply lintegral_mono
    intro z
    exact hSqBound p z

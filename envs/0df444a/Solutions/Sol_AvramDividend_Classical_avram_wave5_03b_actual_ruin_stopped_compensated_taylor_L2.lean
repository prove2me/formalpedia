-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_compensated_taylor_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:12:24.632212+00:00
-- url     : https://prove2.me/submissions/19b0247b-2155-4141-ba7c-3568a3c72736

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_compensated_full_negative_mark_predictable_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_ruinTime_rightCont_stopping_time

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original ruin-stopped compensated negative jump Taylor remainder
retains the quadratic energy of its predictable unrestricted kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
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
      (inferInstance : MeasurableSpace ℝ)] HS ∧
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((HS (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by
  dsimp only
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then
      p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
      else 0)
  let S : ℝ≥0 × Ω → ℝ := fun p =>
    if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => S p.1 * H p
  have hbase : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H ∧
      (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ :=
    avram_wave4_04b_controlled_compensated_full_negative_mark_predictable_L2_energy
      X x D hD w a b u v δ hw hw_cont hw_neg
      hau huv hvb hu0 hδ hδone hband μ hμ
  have hτ : IsStoppingTime 𝓕.rightCont (ruinTime X x D) :=
    avram_wave4_03_actual_ruinTime_rightCont_stopping_time X x D hD
  have hSstrong : IsStronglyPredictable 𝓕.rightCont
      (fun t ω => if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0) :=
    avram_wave3_04_inclusiveSurvival_stronglyPredictable
      (ruinTime X x D) hτ
  change StronglyMeasurable[𝓕.rightCont.predictable] S at hSstrong
  have hSmeas : Measurable[𝓕.rightCont.predictable] S :=
    hSstrong.measurable
  change Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] HS ∧
      (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((HS (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)
  have hSmark : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) => S p.1) :=
    hSmeas.comp measurable_fst
  refine ⟨hSmark.mul hbase.1, ?_⟩
  have hpoint (p : ((ℝ≥0 × Ω) × ℝ)) :
      (HS p) ^ 2 ≤ (H p) ^ 2 := by
    by_cases hp : (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2
    · simp [HS, S, hp]
    · simpa [HS, S, hp] using (sq_nonneg (H p))
  have hinner (p : ℝ≥0 × Ω) :
      (∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((HS (p, z)) ^ 2) ∂X.ν) ≤
      (∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν) := by
    have hpair : Measurable (fun z : ℝ => (p, z)) := by fun_prop
    have hHsection : Measurable (fun z : ℝ => H (p, z)) :=
      hbase.1.comp hpair
    have hHsq : Measurable (fun z : ℝ =>
        ENNReal.ofReal ((H (p, z)) ^ 2)) :=
      ENNReal.measurable_ofReal.comp (hHsection.pow_const 2)
    apply setLIntegral_mono hHsq
    intro z hz
    exact ENNReal.ofReal_le_ofReal (hpoint (p, z))
  exact lt_of_le_of_lt (lintegral_mono hinner) hbase.2

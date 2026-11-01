-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_actual_ruin_stopped_full_jump_l2_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:59:42.669639+00:00
-- url     : https://prove2.me/submissions/8fd484c2-2e83-41e8-8134-4f3b7cceba0d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_ruinTime_rightCont_stopping_time

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Inclusive endogenous ruin stopping preserves full source-jump L² energy and predictability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let J : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      fun p => if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * J p
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H ∧
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by
  dsimp only
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let J : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
    fun p => if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * J p
  change Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H ∧
    (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤
  have hJ :=
    avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite
      X x D hD w a b u v δ hw hw_cont hw_neg
      hau huv hvb hu0 hδ hδone hband μ hμ
  have hτ : IsStoppingTime 𝓕.rightCont (ruinTime X x D) :=
    avram_wave4_03_actual_ruinTime_rightCont_stopping_time X x D hD
  have hS :
      IsStronglyPredictable 𝓕.rightCont
        (fun t ω => if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0) :=
    avram_wave3_04_inclusiveSurvival_stronglyPredictable _ hτ
  change StronglyMeasurable[𝓕.rightCont.predictable]
    (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) at hS
  have hSm : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω =>
        if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) :=
    hS.measurable
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)
  have hSmMark : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) :=
    hSm.comp measurable_fst
  refine ⟨hSmMark.mul hJ.1, ?_⟩
  have hpoint (p : ((ℝ≥0 × Ω) × ℝ)) :
      (H p) ^ 2 ≤ (J p) ^ 2 := by
    by_cases hs : (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2
    · simp [H, hs]
    · simpa [H, hs] using (sq_nonneg (J p))
  calc
    (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) ≤
      (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((J (p, z)) ^ 2) ∂X.ν ∂μ) := by
        apply lintegral_mono
        intro p
        apply lintegral_mono
        intro z
        exact ENNReal.ofReal_le_ofReal (hpoint (p, z))
    _ < ⊤ := hJ.2

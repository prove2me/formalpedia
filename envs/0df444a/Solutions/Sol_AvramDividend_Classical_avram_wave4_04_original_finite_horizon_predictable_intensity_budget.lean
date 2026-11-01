-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_original_finite_horizon_predictable_intensity_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:45:59.018705+00:00
-- url     : https://prove2.me/submissions/280983b4-8754-4c25-92e8-699f365c24fd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

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
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
         (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
       let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
         fun p => if Y p.1 ∈ Icc (u + δ) v then
           w (Y p.1 + p.2) - w (Y p.1) else 0
       Measurable[(𝓕.rightCont.predictable).prod
         (inferInstance : MeasurableSpace ℝ)] H ∧
       (∫⁻ p : ℝ≥0 × Ω,
         ∫⁻ z in Iio (0 : ℝ),
           ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hcompact : IsCompact (Icc (0 : ℝ) (T : ℝ)) := isCompact_Icc
  have hT : (volume : Measure ℝ) (Icc 0 (T : ℝ)) < ⊤ :=
    hcompact.measure_lt_top
  let ηReal : Measure ℝ := (volume : Measure ℝ).restrict (Icc 0 (T : ℝ))
  have hηReal : ηReal Set.univ < ⊤ := by simpa [ηReal] using hT
  letI : IsFiniteMeasure ηReal := ⟨hηReal⟩
  let η : Measure ℝ≥0 := ηReal.map Real.toNNReal
  letI : IsFiniteMeasure η := Measure.isFiniteMeasure_map ηReal Real.toNNReal
  let ξ : Measure (ℝ≥0 × Ω) := η.prod P
  letI : IsFiniteMeasure ξ := by dsimp [ξ]; infer_instance
  have hpred : 𝓕.rightCont.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply MeasureTheory.measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      exact (measurableSet_singleton (⊥ : ℝ≥0)).prod ((𝓕.rightCont.le ⊥) A hA)
    · intro i A hA
      exact (measurableSet_Ioi).prod ((𝓕.rightCont.le i) A hA)
  let μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable) := ξ.trim hpred
  have hμ : μ Set.univ < ⊤ := by
    letI : IsFiniteMeasure μ := isFiniteMeasure_trim hpred
    exact measure_lt_top _ _
  refine ⟨μ, hμ, ?_, ?_⟩
  · intro A hA
    change ξ.trim hpred A = ξ A
    exact trim_measurableSet_eq hpred hA
  · exact avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite
      X x D hD w a b u v δ hw hw_cont hw_neg
      hau huv hvb hu0 hδ hδone hband μ hμ

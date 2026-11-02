-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_rightcont_stopped_source_initial_compensator_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:56:04.600477+00:00
-- url     : https://prove2.me/submissions/8900a24c-f7c7-44d9-801e-159a048a45e4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_predictable_occupation_bottom_rectangle_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_rightcont_canonical_levy_intensity_initial_rectangle_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The literal source stopped jump occupation and its actual canonical
Levy intensity agree at the predictable initial-time rectangles. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (MT : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
        ∀ (B : Set ℝ), MeasurableSet B →
        MT (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B) =
          (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
           μ.prod (X.ν.restrict (Iio (0 : ℝ))))
            (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B)) := by
  obtain ⟨Y, hYX, _hc, _hσ, _hν⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  have hKY : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ Y.X u ω -
            Function.leftLim (fun v : ℝ≥0 => Y.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, Y.X u ω -
            Function.leftLim (fun v : ℝ≥0 => Y.X v ω) u))) := by
    intro ω
    simpa only [hYX] using hK ω
  obtain ⟨μ, hfin, hagree, hμzero⟩ :=
    avram_wave5_01_actual_rightcont_canonical_levy_intensity_initial_rectangle_zero X T
  refine ⟨μ, hfin, hagree, ?_⟩
  intro A hA B hB
  have hMzero :
      M (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B) = 0 :=
    avram_wave5_01_actual_source_predictable_occupation_bottom_rectangle_zero
      Y K hKY M hM A hA B hB
  have hPred : MeasurableSet[𝓕.rightCont.predictable]
      ({(0 : ℝ≥0)} ×ˢ A) :=
    measurableSet_predictable_singleton_bot_prod hA
  have hC : MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B) := hPred.prod hB
  have hMTzero :
      MT (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B) = 0 := by
    rw [hMT, Measure.restrict_apply hC]
    apply le_antisymm
    · exact (measure_mono Set.inter_subset_left).trans hMzero.le
    · exact bot_le
  rw [hMTzero, hμzero A hA B hB]

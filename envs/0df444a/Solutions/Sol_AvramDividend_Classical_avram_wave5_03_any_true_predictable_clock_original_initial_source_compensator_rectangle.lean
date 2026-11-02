-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_any_true_predictable_clock_original_initial_source_compensator_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:40:25.38793+00:00
-- url     : https://prove2.me/submissions/f7511b19-c1ae-4e34-942a-4863cdea165b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_rightcont_stopped_source_initial_compensator_rectangle
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A genuine physical predictable clock uniquely fixes the source initial compensation. -/
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
    (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) :
    ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      ∀ (B : Set ℝ), MeasurableSet B →
      MT (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B) =
        (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
         μ.prod (X.ν.restrict (Iio (0 : ℝ))))
          (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B) := by
  classical
  obtain ⟨μ', hμ'finite, hμ'clock, hBot⟩ :=
    avram_wave5_01_actual_rightcont_stopped_source_initial_compensator_rectangle
      X K hK M hM S MT hMT T
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hμeq : μ = μ' := by
    apply Measure.ext
    intro A hA
    exact (hμclock A hA).trans (hμ'clock A hA).symm
  intro A hA B hB
  simpa only [hμeq] using hBot A hA B hB

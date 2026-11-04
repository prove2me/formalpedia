-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_P2_intrinsic_rate_to_actual_stopped_rightcont_future
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:12:42.262421+00:00
-- url     : https://prove2.me/submissions/a9f28b3e-bd72-4887-a153-bf90cec5df5f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_intrinsic_rect_rate_to_occupation
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_P2_rate_implies_stopped_source_rightcont_future
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original P2 intrinsic marked rate implies genuine stopped predictable future. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω = ((Measure.count.restrict
      {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω = @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
      (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))
      (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (MK : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hMK : MK = P.bind K)
    (hP2 : ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω in A, NX ω (Ioc s t ×ˢ B) ∂P) =
          P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ E : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] E →
      μ E = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) E)
    (N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (i : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[𝓕.rightCont i] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (MK.restrict {p | p.1.1 ≤ T}) ((Ioi i ×ˢ A) ×ˢ B) =
      N ((Ioi i ×ˢ A) ×ˢ B) := by
  apply avram_p3_b_bvjump_original_P2_rate_implies_stopped_source_rightcont_future
    X T MK ?_ μ hμclock N hN i A hA B hB
  intro s t hst A' hA' B' hB'
  apply avram_p3_b_bvjump_original_intrinsic_rect_rate_to_occupation
    X K ?_ MK hMK ?_ s t hst A' hA' B' hB'
  · intro ω
    simpa only [hNX ω] using hK ω
  · intro s' t' hst' A'' hA'' B'' hB''
    simpa only [hNX] using hP2 s' t' hst' A'' hA'' B'' hB''

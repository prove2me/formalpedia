-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_intrinsic_rect_rate_to_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:40:55.469707+00:00
-- url     : https://prove2.me/submissions/c815618e-0f19-49b4-9d9e-d433af1b96ca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_rightcont_source_predictable_adapted_rectangle_eq_intrinsic_lintegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∀ (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _
          (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (hRate : ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω in A, NX ω (Ioc s t ×ˢ B) ∂P) =
          P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B),
      M ((Ioc s t ×ˢ A) ×ˢ B) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  intro NX K hK M hM hRate s t hst A hA B hB
  calc
    M ((Ioc s t ×ˢ A) ×ˢ B) =
        (∫⁻ ω in A, NX ω (Ioc s t ×ˢ B) ∂P) := by
      exact avram_wave5_01_actual_rightcont_source_predictable_adapted_rectangle_eq_intrinsic_lintegral
        X K hK M hM s t A ((𝓕.le_rightCont s A) hA) B hB
    _ = P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B :=
      hRate s t hst A hA B hB

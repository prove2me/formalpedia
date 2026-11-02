-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_rightcont_source_predictable_adapted_rectangle_eq_intrinsic_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:34:02.661478+00:00
-- url     : https://prove2.me/submissions/78b2c838-679f-400f-8611-058a75e5c2d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_original_rightcont_predictable_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_joint_original_predictable_mark_lift_measurable
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Exact same-path source occupation identity on every original-past
adapted marked rectangle; no Lévy intensity law is assumed. -/
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
    (s t : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    M (((Ioc s t) ×ˢ A) ×ˢ B) =
      (∫⁻ ω in A,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          ((Ioc s t) ×ˢ B) ∂P) := by
  classical
  have hKm : AEMeasurable K P :=
    avram_wave5_02a_original_rightcont_predictable_kernel_measurable X K hK
  have hPred : MeasurableSet[𝓕.rightCont.predictable] ((Ioc s t) ×ˢ A) :=
    measurableSet_predictable_Ioc_prod s t hA
  have hC : MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      (((Ioc s t) ×ˢ A) ×ˢ B) := hPred.prod hB
  have hAg : MeasurableSet A := (𝓕.rightCont.le s) A hA
  have hLift (ω : Ω) :
      @Measurable (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) := by
    have hJoint :=
      avram_wave5_02a_joint_original_predictable_mark_lift_measurable 𝓕.rightCont
    have hPair : Measurable (fun p : ℝ≥0 × ℝ => (p, ω)) :=
      measurable_id.prodMk measurable_const
    exact hJoint.comp hPair
  let J : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      ((Ioc s t) ×ˢ B)
  have hPreimage (ω : Ω) :
      (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) ⁻¹'
        (((Ioc s t) ×ˢ A) ×ˢ B) =
        if ω ∈ A then ((Ioc s t) ×ˢ B) else ∅ := by
    ext p
    by_cases hω : ω ∈ A
    · simp only [hω, ite_true]
      simp [Set.mem_prod, hω]
    · simp only [hω, ite_false]
      simp [Set.mem_prod, hω]
  have hKpoint (ω : Ω) :
      K ω (((Ioc s t) ×ˢ A) ×ˢ B) =
        A.indicator J ω := by
    rw [hK ω, Measure.map_apply (hLift ω) hC, hPreimage ω]
    by_cases hω : ω ∈ A
    · simp [Set.indicator, hω, J]
    · simp [Set.indicator, hω]
  calc
    M (((Ioc s t) ×ˢ A) ×ˢ B) =
        ∫⁻ ω, K ω (((Ioc s t) ×ˢ A) ×ˢ B) ∂P := by
      rw [hM, Measure.bind_apply hC hKm]
    _ = ∫⁻ ω, A.indicator J ω ∂P :=
      lintegral_congr hKpoint
    _ = ∫⁻ ω in A, J ω ∂P :=
      lintegral_indicator hAg J

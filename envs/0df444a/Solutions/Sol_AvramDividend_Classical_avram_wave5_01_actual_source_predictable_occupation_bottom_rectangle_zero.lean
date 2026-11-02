-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_predictable_occupation_bottom_rectangle_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:25:12.111789+00:00
-- url     : https://prove2.me/submissions/afd982ac-89b8-4bf4-845b-2be122a97bf9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_full_original_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_joint_original_predictable_mark_lift_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_zero_initial_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The predictable occupation of the genuine original Lévy jump kernel
charges no initial-time marked rectangle. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (A : Set Ω) (hA : MeasurableSet[𝓕 0] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    M (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B) = 0 := by
  have hKm : AEMeasurable K P :=
    avram_wave5_02a_full_original_kernel_measurable X K hK
  have hPred : MeasurableSet[𝓕.predictable]
      ({(0 : ℝ≥0)} ×ˢ A) := by
    exact measurableSet_predictable_singleton_bot_prod hA
  have hC : MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))]
      (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B) := hPred.prod hB
  have hLift (ω : Ω) :
      @Measurable (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) := by
    have hJoint :=
      avram_wave5_02a_joint_original_predictable_mark_lift_measurable 𝓕
    have hPair : Measurable (fun p : ℝ≥0 × ℝ => (p, ω)) :=
      measurable_id.prodMk measurable_const
    exact hJoint.comp hPair
  have hZero (ω : Ω) :
      K ω (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B) = 0 := by
    rw [hK ω, Measure.map_apply (hLift ω) hC]
    have hsub :
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) ⁻¹'
          (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B) ⊆
          ({(0 : ℝ≥0)} ×ˢ B) := by
      intro p hp
      exact ⟨hp.1.1, hp.2⟩
    apply le_antisymm
    · exact (measure_mono hsub).trans
        (avram_wave5_01_actual_source_jump_measure_zero_initial_time
          X ω B hB).le
    · exact bot_le
  rw [hM, Measure.bind_apply hC hKm]
  simp [hZero]

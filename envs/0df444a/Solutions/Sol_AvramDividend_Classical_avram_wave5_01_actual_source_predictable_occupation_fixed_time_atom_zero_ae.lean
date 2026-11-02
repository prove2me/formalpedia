-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_predictable_occupation_fixed_time_atom_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:36:09.674441+00:00
-- url     : https://prove2.me/submissions/18246a27-8dd9-460f-9fff-ed4c40c86c51

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_full_original_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_joint_original_predictable_mark_lift_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_zero_initial_time
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_fixed_time_marked_count_zero_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Predictable source occupation at every deterministic time has no
marked atom, with the unchanged original process and filtration. -/
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
    (t : ℝ≥0) (A : Set Ω)
    (hPred : MeasurableSet[𝓕.predictable] ({t} ×ˢ A))
    (B : Set ℝ) (hB : MeasurableSet B) :
    M (({t} ×ˢ A) ×ˢ B) = 0 := by
  have hKm : AEMeasurable K P :=
    avram_wave5_02a_full_original_kernel_measurable X K hK
  have hC : MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))]
      (({t} ×ˢ A) ×ˢ B) := hPred.prod hB
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
  have hCountZero : ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        ({t} ×ˢ B) = 0 := by
    by_cases ht : t = 0
    · subst t
      exact Filter.Eventually.of_forall (fun ω =>
        avram_wave5_01_actual_source_jump_measure_zero_initial_time
          X ω B hB)
    · have htpos : 0 < t := pos_iff_ne_zero.mpr ht
      exact avram_wave5_01_actual_source_fixed_time_marked_count_zero_ae
        X t htpos B hB
  have hKzero : ∀ᵐ ω ∂P, K ω (({t} ×ˢ A) ×ˢ B) = 0 := by
    filter_upwards [hCountZero] with ω hω
    rw [hK ω, Measure.map_apply (hLift ω) hC]
    have hsub :
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) ⁻¹'
          (({t} ×ˢ A) ×ˢ B) ⊆ ({t} ×ˢ B) := by
      intro p hp
      exact ⟨hp.1.1, hp.2⟩
    apply le_antisymm
    · exact (measure_mono hsub).trans hω.le
    · exact bot_le
  calc
    M (({t} ×ˢ A) ×ˢ B) =
        ∫⁻ ω, K ω (({t} ×ˢ A) ×ˢ B) ∂P := by
      rw [hM, Measure.bind_apply hC hKm]
    _ = ∫⁻ _ω, (0 : ℝ≥0∞) ∂P := lintegral_congr_ae hKzero
    _ = 0 := by simp

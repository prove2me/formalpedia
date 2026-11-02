-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_atomless_time_marks_zero_original_probability_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:01:38.869112+00:00
-- url     : https://prove2.me/submissions/fb70b0d1-adf5-43e4-a19f-e73999848560

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_all_original_levy_jump_times_countable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- For the actual source paths, an arbitrary atomless s-finite time law
almost surely charges no jump times under the original probability law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ t : ℝ≥0 ∂μ,
      ∀ᵐ ω ∂P,
        ¬ (0 < t ∧
          X.X t ω -
            Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≠ 0) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let J : Ω × ℝ≥0 → ℝ := fun z =>
    X.X z.2 z.1 - Function.leftLim (fun u : ℝ≥0 => X.X u z.1) z.2
  have hJ : Measurable J := by
    exact (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp
      measurable_swap
  have hJne : MeasurableSet {z : Ω × ℝ≥0 | J z ≠ 0} := by
    have hh : MeasurableSet (J ⁻¹' ({(0 : ℝ)}ᶜ)) :=
      ((measurableSet_singleton (0 : ℝ)).compl).preimage hJ
    simpa [Set.preimage] using hh
  have hS : MeasurableSet
      {z : Ω × ℝ≥0 | 0 < z.2 ∧ J z ≠ 0} :=
    (measurableSet_lt measurable_const measurable_snd).inter hJne
  have hω (ω : Ω) :
      ∀ᵐ t : ℝ≥0 ∂μ,
        ¬ (0 < t ∧ J (ω, t) ≠ 0) := by
    apply (mem_ae_iff).2
    have hCount :
        Set.Countable {t : ℝ≥0 | 0 < t ∧
          X.X t ω - Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≠ 0} := by
      simpa only [sub_ne_zero] using
        avram_wave4_p2_all_original_levy_jump_times_countable X ω
    simpa only [Set.compl_setOf, not_not, J] using (hCount.measure_zero μ)
  have hω_all :
      ∀ᵐ ω ∂P, ∀ᵐ t : ℝ≥0 ∂μ,
        ¬ (0 < t ∧ J (ω, t) ≠ 0) :=
    Filter.Eventually.of_forall hω
  have hswap := (Measure.ae_ae_comm hS.compl).mp hω_all
  simpa only [J] using hswap

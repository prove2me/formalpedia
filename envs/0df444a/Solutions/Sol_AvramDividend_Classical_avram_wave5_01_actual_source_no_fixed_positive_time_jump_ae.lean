-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:49:57.358797+00:00
-- url     : https://prove2.me/submissions/70a679b9-eda2-4921-90a3-eb03c14c8386

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_original_raw_filtration_prejump_jumpmark_strongly_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P, X.X t ω - Function.leftLim (fun u : ℝ≥0 => X.X u ω) t = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let D : Ω → ℝ := fun ω => X.X t ω - Function.leftLim (fun u : ℝ≥0 => X.X u ω) t
  let U : ℝ≥0 → Ω → ℝ := fun s ω => X.X t ω - X.X (min s t) ω
  let V : ℝ≥0 → Ω → ℝ := fun s ω => X.X (t - min s t) ω
  have hDsm : StronglyMeasurable[𝓕 t] D :=
    (avram_wave5_01_actual_original_raw_filtration_prejump_jumpmark_strongly_adapted X).2 t
  have hDm : Measurable D := hDsm.measurable.mono (𝓕.le t) le_rfl
  have hLeft (ω : Ω) :
      Tendsto (fun s : ℝ≥0 => U s ω) (𝓝[<] t) (𝓝 (D ω)) := by
    have hl : Tendsto (fun s : ℝ≥0 => X.X s ω) (𝓝[<] t)
        (𝓝 (Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)) :=
      tendsto_leftLim_of_tendsto (X.leftLim ω t ht)
    have hevent : (fun s : ℝ≥0 => U s ω) =ᶠ[𝓝[<] t]
        (fun s : ℝ≥0 => X.X t ω - X.X s ω) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hst : s < t := Set.mem_Iio.mp hs
      simp only [U, min_eq_left (le_of_lt hst)]
    exact (tendsto_const_nhds.sub hl).congr' hevent.symm
  have hTime : Tendsto (fun s : ℝ≥0 => t - min s t) (𝓝[<] t) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ≥0 => t - min s t) :=
      continuous_const.sub (continuous_id.min continuous_const)
    have hh := (hc.tendsto t).mono_left
      (show 𝓝[<] t ≤ 𝓝 t from nhdsWithin_le_nhds)
    simpa using hh
  have hRight (ω : Ω) :
      Tendsto (fun s : ℝ≥0 => V s ω) (𝓝[<] t) (𝓝 (0 : ℝ)) := by
    have hrc : Tendsto (fun u : ℝ≥0 => X.X u ω) (𝓝 (0 : ℝ≥0))
        (𝓝 (0 : ℝ)) := by
      simpa [X.X_zero ω] using (X.rightCont ω 0).tendsto
    exact hrc.comp hTime
  have hUd : TendstoInDistribution U (𝓝[<] t) D (fun _ => P) P := by
    apply tendstoInDistribution_of_ae_tendsto
    · intro s
      exact ((X.adapted.measurable (i := t)).sub
        (X.adapted.measurable (i := min s t))).aemeasurable
    · exact hDm.aemeasurable
    · exact Filter.Eventually.of_forall hLeft
  have hVd : TendstoInDistribution V (𝓝[<] t)
      (fun _ : Ω => (0 : ℝ)) (fun _ => P) P := by
    apply tendstoInDistribution_of_ae_tendsto
    · intro s
      exact (X.adapted.measurable (i := t - min s t)).aemeasurable
    · exact measurable_const.aemeasurable
    · exact Filter.Eventually.of_forall hRight
  have hLaw (s : ℝ≥0) : Measure.map (U s) P = Measure.map (V s) P := by
    exact (X.stationaryIncrements (min s t) t (min_le_right s t)).map_eq
  haveI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hUd0 : TendstoInDistribution U (𝓝[<] t)
      (fun _ : Ω => (0 : ℝ)) (fun _ => P) P := by
    refine TendstoInDistribution.mk
      (fun s => ((X.adapted.measurable (i := t)).sub
        (X.adapted.measurable (i := min s t))).aemeasurable)
      measurable_const.aemeasurable ?_
    simpa only [hLaw] using hVd.tendsto
  have hMap : Measure.map D P = Measure.map (fun _ : Ω => (0 : ℝ)) P :=
    tendstoInDistribution_unique U hUd hUd0
  have hZero : P {ω : Ω | D ω ≠ 0} = 0 := by
    have hh := congrArg (fun m : Measure ℝ => m ({(0 : ℝ)}ᶜ)) hMap
    rw [Measure.map_apply hDm (measurableSet_singleton (0 : ℝ)).compl] at hh
    simpa [Measure.map_const, Set.preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff] using hh
  change ∀ᵐ ω ∂P, D ω = 0
  apply (mem_ae_iff).2
  simpa only [Set.compl_setOf, not_not] using hZero

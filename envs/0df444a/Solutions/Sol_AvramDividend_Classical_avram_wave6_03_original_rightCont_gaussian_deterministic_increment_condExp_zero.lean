-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:35:06.772899+00:00
-- url     : https://prove2.me/submissions/47d1e3a8-84ff-408a-859c-260f18e5aae2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_indepIncrements_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_drift_centered_increment_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Integrable original-process Gaussian martingale difference given its
right-continuous deterministic-time history, including sigma zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (s t : ℝ≥0) (hst : s ≤ t) :
    let Y : Ω → ℝ := fun ω => X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    Integrable Y P ∧
      (P[Y | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ))) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → ℝ := fun ω => X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
  have hτevents : ∀ u : ℝ≥0,
      MeasurableSet[𝓕.rightCont u]
        {ω : Ω | (fun _ : Ω => s) ω ≤ u} := by
    intro u
    by_cases hsu : s ≤ u <;> simp [hsu]
  have hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => ((fun _ : Ω => s) ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events (fun _ : Ω => s) hτevents
  have hτbound : ∀ ω : Ω, (fun _ : Ω => s) ω ≤ s :=
    fun _ => le_rfl
  have hYMem : MemLp Y 2 P := by
    have hm :=
      avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
        X hν (fun _ : Ω => s) hτstop s hτbound (t - s)
    simpa only [Y, add_tsub_cancel_of_le hst, NNReal.coe_sub hst] using hm
  have hYI : Integrable Y P :=
    hYMem.integrable (by norm_num)
  have hMean : (∫ ω, Y ω ∂P) = 0 := by
    have hm :=
      avram_wave5_03a_actual_rightCont_stopped_gaussian_drift_centered_increment_mean_zero
        X hν (fun _ : Ω => s) hτstop s hτbound (t - s)
    simpa only [Y, add_tsub_cancel_of_le hst, NNReal.coe_sub hst] using hm
  have hXt : StronglyMeasurable (X.X t) :=
    ((X.adapted t).mono (𝓕.le t) le_rfl).stronglyMeasurable
  have hXs : StronglyMeasurable (X.X s) :=
    ((X.adapted s).mono (𝓕.le s) le_rfl).stronglyMeasurable
  have hYsm : StronglyMeasurable Y :=
    (hXt.sub hXs).sub stronglyMeasurable_const
  let R : Ω → ℝ := fun ω => X.X t ω - X.X s ω
  have hRcomap : Measurable[MeasurableSpace.comap R inferInstance] R :=
    comap_measurable R
  have hYcomap : Measurable[MeasurableSpace.comap R inferInstance] Y :=
    hRcomap.sub_const (((t - s) : ℝ) * X.c)
  have hInd : Indep (MeasurableSpace.comap Y inferInstance)
      (𝓕.rightCont s) P :=
    indep_of_indep_of_le
      (show Indep (MeasurableSpace.comap R inferInstance)
        (𝓕.rightCont s) P from
          levy_indepIncrements_rightCont X s t hst)
      hYcomap.comap_le le_rfl
  have hCE : P[Y | 𝓕.rightCont s] =ᵐ[P]
      (fun _ => ∫ ω, Y ω ∂P) :=
    condExp_indep_eq hYsm.measurable.comap_le
      ((𝓕.rightCont).le s) (comap_measurable Y).stronglyMeasurable hInd
  change Integrable Y P ∧
    (P[Y | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ)))
  exact ⟨hYI, by simpa only [hMean] using hCE⟩

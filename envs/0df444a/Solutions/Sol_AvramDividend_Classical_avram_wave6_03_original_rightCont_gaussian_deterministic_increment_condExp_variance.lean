-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:46:23.239269+00:00
-- url     : https://prove2.me/submissions/1842ccde-2d86-4ed6-adde-19ccd46810fa

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_indepIncrements_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Actual source Gaussian squared increments have deterministic right-continuous
conditional variance, including when the source diffusion coefficient is zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (s t : ℝ≥0) (hst : s ≤ t) :
    let Y : Ω → ℝ := fun ω => X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    Integrable (fun ω => Y ω ^ 2) P ∧
      (P[(fun ω => Y ω ^ 2) | 𝓕.rightCont s] =ᵐ[P]
         (fun _ => ((t - s) : ℝ) * X.σ ^ 2)) := by
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
  have hYsqI : Integrable (fun ω => Y ω ^ 2) P :=
    (memLp_two_iff_integrable_sq hYMem.aestronglyMeasurable).mp hYMem
  have hVariance : (∫ ω, Y ω ^ 2 ∂P) = ((t - s) : ℝ) * X.σ ^ 2 := by
    have hm :=
      avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
        X hν (fun _ : Ω => s) hτstop s hτbound (t - s)
    simpa only [Y, add_tsub_cancel_of_le hst, NNReal.coe_sub hst] using hm
  have hXt : StronglyMeasurable (X.X t) :=
    ((X.adapted t).mono (𝓕.le t) le_rfl).stronglyMeasurable
  have hXs : StronglyMeasurable (X.X s) :=
    ((X.adapted s).mono (𝓕.le s) le_rfl).stronglyMeasurable
  have hYsm : StronglyMeasurable Y :=
    (hXt.sub hXs).sub stronglyMeasurable_const
  have hYsqSm : StronglyMeasurable (fun ω => Y ω ^ 2) := by
    convert hYsm.mul hYsm using 1
    funext ω
    simp [Pi.mul_apply, pow_two]
  let R : Ω → ℝ := fun ω => X.X t ω - X.X s ω
  have hRcomap : Measurable[MeasurableSpace.comap R inferInstance] R :=
    comap_measurable R
  have hYcomap : Measurable[MeasurableSpace.comap R inferInstance] Y :=
    hRcomap.sub_const (((t - s) : ℝ) * X.c)
  have hIndY : Indep (MeasurableSpace.comap Y inferInstance)
      (𝓕.rightCont s) P :=
    indep_of_indep_of_le
      (show Indep (MeasurableSpace.comap R inferInstance)
        (𝓕.rightCont s) P from
          levy_indepIncrements_rightCont X s t hst)
      hYcomap.comap_le le_rfl
  have hYsqComap : Measurable[MeasurableSpace.comap Y inferInstance]
      (fun ω => Y ω ^ 2) := by
    convert (comap_measurable Y).mul (comap_measurable Y) using 1
    funext ω
    simp [Pi.mul_apply, pow_two]
  have hIndSq : Indep (MeasurableSpace.comap (fun ω => Y ω ^ 2) inferInstance)
      (𝓕.rightCont s) P :=
    indep_of_indep_of_le hIndY hYsqComap.comap_le le_rfl
  have hCE : P[(fun ω => Y ω ^ 2) | 𝓕.rightCont s] =ᵐ[P]
      (fun _ => ∫ ω, Y ω ^ 2 ∂P) :=
    condExp_indep_eq hYsqSm.measurable.comap_le
      ((𝓕.rightCont).le s)
      (comap_measurable (fun ω => Y ω ^ 2)).stronglyMeasurable hIndSq
  change Integrable (fun ω => Y ω ^ 2) P ∧
    (P[(fun ω => Y ω ^ 2) | 𝓕.rightCont s] =ᵐ[P]
      (fun _ => ((t - s) : ℝ) * X.σ ^ 2))
  exact ⟨hYsqI, by simpa only [hVariance] using hCE⟩

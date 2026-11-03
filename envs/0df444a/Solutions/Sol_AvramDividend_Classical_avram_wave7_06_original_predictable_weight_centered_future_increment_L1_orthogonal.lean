-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_predictable_weight_centered_future_increment_L1_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:59:10.592406+00:00
-- url     : https://prove2.me/submissions/ccf6d5ee-e8cf-4a5e-801f-82437b0b1e61

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_shifted_future_increment_centered_L1_zero_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original predictable scalar weight is orthogonal in L¹ to its actual centred
future Lévy increment; independence also justifies the product integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (W : Ω → ℝ)
    (hWPast : Measurable[𝓕 s] W)
    (hWI : Integrable W P)
    (hXI : Integrable (X.X t) P) :
    (∫ ω, W ω *
      (X.X (s + t) ω - X.X s ω -
        (∫ η, X.X t η ∂P)) ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let A : Ω → ℝ := fun ω => X.X (s + t) ω - X.X s ω
  let m : ℝ := ∫ η, X.X t η ∂P
  obtain ⟨hCentInt, hCentZero⟩ :=
    avram_wave7_06_original_shifted_future_increment_centered_L1_zero_mean
      X s t hXI
  have hCI : Integrable (fun ω => A ω - m) P := hCentInt
  have hCZ : (∫ ω, A ω - m ∂P) = 0 := hCentZero
  have hWComap : MeasurableSpace.comap W inferInstance ≤ 𝓕 s :=
    (measurable_iff_comap_le).mp hWPast
  have hRawIndep : Indep
      (MeasurableSpace.comap A inferInstance) (𝓕 s) P := by
    simpa only [A] using X.indepIncrements s (s + t) (by simp)
  have hFunIndep : IndepFun W A P := by
    apply (IndepFun_iff_Indep W A P).2
    exact indep_of_indep_of_le hRawIndep.symm hWComap le_rfl
  have hCenterMeas : Measurable (fun y : ℝ => y - m) :=
    measurable_id.sub measurable_const
  have hCenteredIndep :
      IndepFun W (fun ω => A ω - m) P := by
    simpa only [Function.comp_def, id_eq] using
      hFunIndep.comp measurable_id hCenterMeas
  have hFactor := hCenteredIndep.integral_mul_eq_mul_integral
    hWI.aestronglyMeasurable hCI.aestronglyMeasurable
  change (∫ ω, W ω * (A ω - m) ∂P) =
    (∫ ω, W ω ∂P) * (∫ ω, A ω - m ∂P) at hFactor
  rw [hCZ, mul_zero] at hFactor
  exact hFactor

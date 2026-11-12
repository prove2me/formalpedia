-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18o_original_X_increment_rightcont_condexp_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:36:21.937541+00:00
-- url     : https://prove2.me/submissions/071fff3c-56de-407f-82a0-21b432c4ce5f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_future_path_indep_rightcont
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original Lévy increment is an evaluation of the future shifted
path, hence has constant conditional expectation given its past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hXs : Integrable (X.X s) P) (hXt : Integrable (X.X t) P) :
    condExp (𝓕.rightCont s) P
      (fun ω => X.X t ω - X.X s ω) =ᵐ[P]
    (fun _ : Ω => ∫ η, X.X t η - X.X s η ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let D : Ω → ℝ := fun ω => X.X t ω - X.X s ω
  let Shift : Ω → (ℝ≥0 → ℝ) :=
    fun ω u => X.X (s + u) ω - X.X s ω
  let W : (ℝ≥0 → ℝ) → ℝ := fun f => f (t - s)
  have hEq : D = W ∘ Shift := by
    funext ω
    change X.X t ω - X.X s ω =
      X.X (s + (t - s)) ω - X.X s ω
    rw [add_tsub_cancel_of_le hst]
  have hMeas : Measurable D := by
    exact ((X.adapted t).mono (𝓕.le t) le_rfl).sub
      ((X.adapted s).mono (𝓕.le s) le_rfl)
  have hFactor : Measurable[MeasurableSpace.comap Shift inferInstance] D := by
    rw [hEq]
    exact (measurable_pi_apply (t - s)).comp
      (measurable_iff_comap_le.mpr le_rfl)
  have hShiftIndep := avram_ja18h_original_future_path_indep_rightcont X s
  have hPast : Indep (𝓕.rightCont s)
      (MeasurableSpace.comap D inferInstance) P :=
    indep_of_indep_of_le_right hShiftIndep hFactor.comap_le
  exact condExp_indep_eq hMeas.comap_le (𝓕.rightCont.le s)
    (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable hPast.symm

-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_gauss14_original_stopped_future_signed_negative_mark_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:30:15.302124+00:00
-- url     : https://prove2.me/submissions/2a74dee2-f625-4883-b2f3-dc8f0a799729

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_generic_negative_mark_window_integral_formula
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_stopped_future_weighted_mark_mass_independent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The signed actual negative-jump mass in a future stopped interval is independent of stopped history. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : ∀ z ∈ B, z ≤ 0) :
    let J : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    Indep
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace
      (MeasurableSpace.comap
        (fun ω : Ω =>
          ∫ p in (Ioc (τ ω) (τ ω + T) ×ˢ B), p.2 ∂J ω)
        inferInstance) P := by
  classical
  let J : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let g : ℝ → ℝ≥0∞ := fun z => if z ∈ B then ENNReal.ofReal (-z) else 0
  have hg : Measurable g := by
    dsimp [g]
    exact Measurable.ite hB
      (ENNReal.measurable_ofReal.comp measurable_neg)
      (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ≥0∞)))
  let Z : Ω → ℝ := fun ω =>
    (∫⁻ p : ℝ≥0 × ℝ,
      if τ ω < p.1 ∧ p.1 ≤ τ ω + T then g p.2 else 0 ∂J ω).toReal
  have hIndZ : Indep
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace
      (MeasurableSpace.comap Z inferInstance) P :=
    avram_mix_gauss14_original_stopped_future_weighted_mark_mass_independent
      X τ hτ T g hg
  have hMeasZ : Measurable[MeasurableSpace.comap Z inferInstance] Z :=
    measurable_iff_comap_le.mpr le_rfl
  have hIndNeg : Indep
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace
      (MeasurableSpace.comap (fun ω => -Z ω) inferInstance) P :=
    indep_of_indep_of_le_right hIndZ hMeasZ.neg.comap_le
  have hEq : (fun ω : Ω =>
      ∫ p in (Ioc (τ ω) (τ ω + T) ×ˢ B), p.2 ∂J ω) =
      (fun ω : Ω => -Z ω) := by
    funext ω
    exact avram_mix_gauss14_generic_negative_mark_window_integral_formula
      (J ω) (τ ω) (τ ω + T) B hB hNeg
  change Indep
    (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace
    (MeasurableSpace.comap
      (fun ω : Ω => ∫ p in (Ioc (τ ω) (τ ω + T) ×ˢ B), p.2 ∂J ω)
      inferInstance) P
  rw [hEq]
  exact hIndNeg

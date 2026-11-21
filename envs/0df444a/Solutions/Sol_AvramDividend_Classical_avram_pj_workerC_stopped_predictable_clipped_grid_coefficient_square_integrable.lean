-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_stopped_predictable_clipped_grid_coefficient_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:38:24.698224+00:00
-- url     : https://prove2.me/submissions/e5938d74-a715-4444-8f0b-92166a8e4b13

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A genuine right-continuously stopped predictable coefficient,
clipped at K, has integrable squared value under the original probability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : IsStronglyPredictable 𝓕.rightCont Z)
    (K : ℝ) (hK : 0 ≤ K)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (t : ℝ≥0) :
    Integrable (fun ω =>
      (if (ρ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)
        then (0 : ℝ) else max (-K) (min K (Z t ω)))^2) P := by
  let L : ℝ≥0 → Ω → ℝ := fun u ω => max (-K) (min K (Z u ω))
  obtain ⟨hPred, hClip⟩ :=
    avram_wave3_04_clipped_stronglyPredictable_bounded Z hZ K hK
  have hL : Measurable (L t) :=
    ((hPred.stronglyAdapted t).mono (𝓕.rightCont.le t)).measurable
  have hSet : MeasurableSet
      {ω : Ω | (ρ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} := by
    exact (𝓕.rightCont.le t) _
      (hρstop.measurableSet_le t)
  have hMask : Measurable (fun ω =>
      if (ρ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)
        then (0 : ℝ) else L t ω) :=
    measurable_const.ite hSet hL
  have hSqMeas : AEStronglyMeasurable (fun ω =>
      (if (ρ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)
        then (0 : ℝ) else L t ω)^2) P :=
    (hMask.pow_const 2).aestronglyMeasurable
  apply Integrable.of_bound hSqMeas (K^2)
  filter_upwards [] with ω
  by_cases hs : (ρ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)
  · rw [if_pos hs]
    simpa only [pow_two, zero_mul, norm_zero] using (sq_nonneg K)
  · have hb : ‖L t ω‖ ≤ K := hClip t ω
    have ha : 0 ≤ K - ‖L t ω‖ := sub_nonneg.mpr hb
    have hc : 0 ≤ K + ‖L t ω‖ := by positivity
    have hsq : ‖L t ω‖^2 ≤ K^2 := by
      nlinarith [mul_nonneg ha hc]
    rw [if_neg hs]
    simpa only [norm_pow] using hsq

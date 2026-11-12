-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb48_centered_fourth_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:09:30.76252+00:00
-- url     : https://prove2.me/submissions/a45abc65-356e-4e7b-b9b1-bf29a2c1fef0

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- A raw fourth-moment integrability bound controls every shifted square. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Measurable Z)
    (hfourth : Integrable (fun ω => Z ω ^ 4) P) (a : ℝ) :
    Integrable (fun ω => (Z ω ^ 2 - a) ^ 2) P ∧
      (∫ ω, (Z ω ^ 2 - a) ^ 2 ∂P) ≤
        2 * (∫ ω, Z ω ^ 4 ∂P) + 2 * a ^ 2 := by
  have hm : Integrable (fun ω => 2 * Z ω ^ 4 + 2 * a ^ 2) P :=
    (hfourth.const_mul 2).add (integrable_const _)
  have hp (ω : Ω) : (Z ω ^ 2 - a) ^ 2 ≤
      2 * Z ω ^ 4 + 2 * a ^ 2 := by
    nlinarith [sq_nonneg (Z ω ^ 2 + a)]
  have hsm : AEStronglyMeasurable (fun ω => (Z ω ^ 2 - a) ^ 2) P :=
    (((hZ.pow_const 2).sub measurable_const).pow_const 2).aestronglyMeasurable
  have hi : Integrable (fun ω => (Z ω ^ 2 - a) ^ 2) P := by
    apply Integrable.mono' hm hsm
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hp ω
  refine ⟨hi, ?_⟩
  calc
    (∫ ω, (Z ω ^ 2 - a) ^ 2 ∂P) ≤
        ∫ ω, 2 * Z ω ^ 4 + 2 * a ^ 2 ∂P :=
      integral_mono hi hm hp
    _ = 2 * (∫ ω, Z ω ^ 4 ∂P) + 2 * a ^ 2 := by
      rw [integral_add, integral_const_mul, integral_const]
      · have hprob : P.real Set.univ = 1 := by
          simp [Measure.real]
        rw [hprob]
        ring
      · exact (hfourth.const_mul 2)
      · exact integrable_const _

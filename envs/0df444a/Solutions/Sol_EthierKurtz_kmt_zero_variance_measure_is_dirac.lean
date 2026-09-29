-- Prove2me | solution 1 for EthierKurtz.kmt_zero_variance_measure_is_dirac
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T02:38:04.674986+00:00
-- url     : https://prove2.me/submissions/b161399d-e0f6-4c27-97bb-940130260921

import Mathlib

open MeasureTheory ProbabilityTheory in
theorem solution
    (mu : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real)))
    (hvar : variance (fun x : Real => x) (mu : Measure Real) = 0) :
    Exists fun m : Real => Measure.map (fun _ : Real => m) (mu : Measure Real) = (mu : Measure Real) := by
  obtain ⟨a0, ha0, hint⟩ := hexp
  have hpos : Integrable (fun x : Real => Real.exp (a0 * x)) (mu : Measure Real) :=
    hint a0 (by rw [abs_of_pos ha0])
  have hneg : Integrable (fun x : Real => Real.exp (-a0 * x)) (mu : Measure Real) :=
    hint (-a0) (by rw [abs_neg, abs_of_pos ha0])
  have hsq : Integrable (fun x : Real => x ^ 2) (mu : Measure Real) :=
    integrable_pow_of_integrable_exp_mul (X := fun x : Real => x) ha0.ne' hpos hneg 2
  have hLp : MemLp (fun x : Real => x) 2 (mu : Measure Real) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hsq
  have hlt : evariance (fun x : Real => x) (mu : Measure Real) < ⊤ :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).2 hLp
  have hev : evariance (fun x : Real => x) (mu : Measure Real) = 0 := by
    have h0 : (evariance (fun x : Real => x) (mu : Measure Real)).toReal = 0 := hvar
    rcases ENNReal.toReal_eq_zero_iff _ |>.1 h0 with h | h
    · exact h
    · exact absurd h hlt.ne
  have hae := (evariance_eq_zero_iff (X := fun x : Real => x) measurable_id.aemeasurable).1 hev
  refine ⟨MeasureTheory.integral (mu : Measure Real) (fun x : Real => x), ?_⟩
  exact (Measure.map_congr hae.symm).trans Measure.map_id'

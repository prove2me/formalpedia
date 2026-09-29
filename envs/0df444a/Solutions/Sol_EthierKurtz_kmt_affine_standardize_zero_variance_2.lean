-- Prove2me | solution 2 for EthierKurtz.kmt_affine_standardize_zero_variance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T05:24:42.034517+00:00
-- url     : https://prove2.me/submissions/7ebdfb7f-ff61-430f-8fc6-5f06b9c1cfea

import Mathlib

open MeasureTheory ProbabilityTheory in
private lemma p2m37e3_exists_dirac
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

open MeasureTheory ProbabilityTheory in
theorem solution
    (mu : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real)))
    (hvar : variance (fun x : Real => x) (mu : Measure Real) = 0) :
    Exists fun (nu : ProbabilityMeasure Real) => Exists fun m : Real => Exists fun sigma : Real =>
      And (0 <= sigma) (And (Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
      (And (MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
      (And (variance (fun y : Real => y) (nu : Measure Real) = 1)
      (Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
        Integrable (fun y : Real => Real.exp (a * y)) (nu : Measure Real)))))) := by
  obtain ⟨m, hm⟩ := p2m37e3_exists_dirac mu hexp hvar
  refine ⟨⟨gaussianReal 0 1, inferInstance⟩, m, 0, le_refl 0, ?_, ?_, ?_, 1, one_pos, fun a _ => ?_⟩
  · have h1 : Measure.map (fun y : Real => m + 0 * y) (gaussianReal 0 1)
        = Measure.map (fun _ : Real => m) (gaussianReal 0 1) := by
      congr 1
      funext y
      simp
    change Measure.map (fun y : Real => m + 0 * y) (gaussianReal 0 1) = (mu : Measure Real)
    rw [h1, Measure.map_const, ← hm, Measure.map_const]
    simp
  · exact integral_id_gaussianReal
  · simp
  · exact integrable_exp_mul_gaussianReal a

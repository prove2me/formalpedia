-- Prove2me | solution 1 for EthierKurtz.affine_standardize_moments_of_pos_variance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T02:32:34.819221+00:00
-- url     : https://prove2.me/submissions/a6dc20c1-cc8f-46ed-aa58-39a4da5fd649

import Mathlib

open MeasureTheory ProbabilityTheory in
theorem solution
    (mu : ProbabilityMeasure Real)
    (hvar : 0 < variance (fun x : Real => x) (mu : Measure Real)) :
    Exists fun (nu : ProbabilityMeasure Real) => Exists fun m : Real => Exists fun sigma : Real =>
      And (0 < sigma) (And (Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
      (And (MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
      (variance (fun y : Real => y) (nu : Measure Real) = 1))) := by
  set V : Real := variance (fun x : Real => x) (mu : Measure Real) with hV
  set m : Real := MeasureTheory.integral (mu : Measure Real) (fun y : Real => y) with hm
  set s : Real := Real.sqrt V with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hvar
  have hsne : s ≠ 0 := hspos.ne'
  have hs2 : s ^ 2 = V := Real.sq_sqrt hvar.le
  have hLp : MemLp (fun y : Real => y) 2 (mu : Measure Real) :=
    memLp_two_of_variance_ne_zero measurable_id.aestronglyMeasurable hvar.ne'
  have hint : Integrable (fun y : Real => y) (mu : Measure Real) :=
    hLp.integrable one_le_two
  let f : Real → Real := fun x => s⁻¹ * (x - m)
  have hf : Measurable f := by fun_prop
  let nu : ProbabilityMeasure Real := mu.map hf.aemeasurable
  have hnu : (nu : Measure Real) = Measure.map f (mu : Measure Real) :=
    ProbabilityMeasure.toMeasure_map mu hf.aemeasurable
  have hg : Measurable (fun y : Real => m + s * y) := by fun_prop
  refine ⟨nu, m, s, hspos, ?_, ?_, ?_⟩
  · rw [hnu, Measure.map_map hg hf]
    have : ((fun y : Real => m + s * y) ∘ f) = id := by
      funext x
      simp only [Function.comp, f, id]
      field_simp
      ring
    rw [this, Measure.map_id]
  · rw [hnu, integral_map hf.aemeasurable (by fun_prop)]
    simp only [f]
    rw [integral_const_mul, integral_sub hint (integrable_const m), integral_const]
    simp [hm]
  · rw [hnu]
    have h1 := variance_id_map (μ := (mu : Measure Real)) hf.aemeasurable
    have h2 := variance_const_mul s⁻¹ (fun x : Real => x - m) (mu : Measure Real)
    have h3 := variance_sub_const (μ := (mu : Measure Real))
      (X := fun x : Real => x) measurable_id.aestronglyMeasurable m
    calc variance (fun y : Real => y) (Measure.map f (mu : Measure Real))
        = variance f (mu : Measure Real) := h1
      _ = s⁻¹ ^ 2 * variance (fun x : Real => x - m) (mu : Measure Real) := h2
      _ = s⁻¹ ^ 2 * V := by rw [h3]
      _ = 1 := by rw [← hs2]; field_simp

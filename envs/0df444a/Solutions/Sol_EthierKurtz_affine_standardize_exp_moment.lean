-- Prove2me | solution 1 for EthierKurtz.affine_standardize_exp_moment
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T07:16:51.113998+00:00
-- url     : https://prove2.me/submissions/820f1470-a840-4771-839d-eeb805fbcf87

import Mathlib

open MeasureTheory ProbabilityTheory in
theorem solution
    (mu nu : ProbabilityMeasure Real) (m sigma : Real)
    (hsigma : 0 < sigma)
    (hmap : Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real))) :
    Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun y : Real => Real.exp (a * y)) (nu : Measure Real)) := by
  obtain ⟨a0, ha0, hint⟩ := hexp
  refine ⟨a0 * sigma, mul_pos ha0 hsigma, fun b hb => ?_⟩
  have hmeas : Measurable (fun y : Real => m + sigma * y) := by fun_prop
  have hab : |b / sigma| ≤ a0 := by
    rw [abs_div, abs_of_pos hsigma, div_le_iff₀ hsigma]
    exact hb
  have h1 := hint (b / sigma) hab
  rw [← hmap, integrable_map_measure (by fun_prop) hmeas.aemeasurable] at h1
  have h2 := h1.const_mul (Real.exp (-(b / sigma * m)))
  refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply]
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

-- Prove2me | solution 1 for BookProof.QgHermiteCore.memLp_abs_poly_mul_exp_neg_eighth
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:23:18.137286+00:00
-- url     : https://prove2.me/submissions/d28c52bb-3a70-47f6-a946-094fc03669cc

import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore MeasureTheory
set_option autoImplicit false

theorem solution (p : Polynomial ℝ) :
    MemLp (fun x : ℝ => ((|p.eval x| * Real.exp (-x ^ 2 / 8) : ℝ) : ℂ)) 2
      (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => ((|p.eval x| * Real.exp (-x ^ 2 / 8) : ℝ) : ℂ)) volume := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine (integrable_poly_mul_exp_neg (p * p) (b := 1 / 4) (by norm_num)).congr
    (Filter.Eventually.of_forall (fun x => ?_))
  have hExp : Real.exp (-x ^ 2 / 8) ^ 2 = Real.exp (-(1 / 4 : ℝ) * x ^ 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [Polynomial.eval_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_abs,
    abs_of_pos (Real.exp_pos _), mul_pow, sq_abs, hExp]
  ring
#print axioms solution

-- Prove2me | solution 1 for BookProof.QgHermiteCore.integrable_gaussPoly_mul
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:11:44.648231+00:00
-- url     : https://prove2.me/submissions/17303c3c-b373-4485-8535-0ddc07ef2851

import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore MeasureTheory
set_option autoImplicit false

theorem solution (p q : Polynomial ℝ) :
    Integrable (fun x : ℝ => (p.eval x * gaussH x) * (q.eval x * gaussH x)) := by
  refine (integrable_poly_mul_gaussW (p * q)).congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [Polynomial.eval_mul]
  rw [← gaussH_sq]
  ring
#print axioms solution

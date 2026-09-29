-- Prove2me | solution 1 for BookProof.QgHermiteCore.memLp_gaussPoly
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:11:45.365311+00:00
-- url     : https://prove2.me/submissions/5fe56894-a952-4dae-b77f-bcb99bca226a

import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore MeasureTheory
set_option autoImplicit false

theorem solution (p : Polynomial ℝ) :
    MemLp (fun x : ℝ => ((p.eval x * gaussH x : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by
  exact memLp_poly_mul_gaussH p
#print axioms solution

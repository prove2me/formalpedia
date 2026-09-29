-- Prove2me | solution 1 for BookProof.QgHermiteCore.integral_gaussPoly_mul
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:11:43.796731+00:00
-- url     : https://prove2.me/submissions/6d6ab8d6-09f5-484e-9fd4-9d4dd99b6bc1

import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore MeasureTheory
set_option autoImplicit false

theorem solution (p q : Polynomial ℝ) :
    ∫ x : ℝ, (p.eval x * gaussH x) * (q.eval x * gaussH x) = gint (p * q) := by
  unfold gint
  apply integral_congr_ae
  filter_upwards with x
  simp only [Polynomial.eval_mul]
  calc
    (p.eval x * gaussH x) * (q.eval x * gaussH x) =
      (p.eval x * q.eval x) * (gaussH x * gaussH x) := by ring
    _ = _ := by rw [gaussH_sq]
#print axioms solution

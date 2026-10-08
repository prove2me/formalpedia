-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.two_le_Vexp
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:14:43.537276+00:00
-- url     : https://prove2.me/submissions/ee6996cb-acb7-49bd-beb7-f60b7512d9d0

-- Generated from ChapterSchrodingerCutoffEsa.lean — theorem BookProof.SchrodingerCutoff.two_le_Vexp
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
open BookProof.SchrodingerCutoff



open MeasureTheory Filter Complex

theorem solution (x : ℝ) : 2 ≤ Vexp x := by
  unfold Vexp
  have h₁ := Real.add_one_le_exp x
  have h₂ := Real.add_one_le_exp (-x)
  linarith

#print axioms solution


-- Prove2me | solution 1 for BookProof.ChapterA3.mgammaR_indep
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:53:38.55859+00:00
-- url     : https://prove2.me/submissions/5dd18591-0006-4abc-8c97-ea0f231870d2

import Mathlib
import Definitions.Def_ChapterA3d
open BookProof.ChapterA3 Matrix
set_option autoImplicit false
set_option maxHeartbeats 0

private lemma indep_local (c : Fin 4 → ℝ)
    (h : ∑ ν, c ν • mgammaR ν = 0) : ∀ ν, c ν = 0 := by
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) h
  have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 2) h
  have h20 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 2 0) h
  norm_num [mgammaR, mgammaZ, Fin.sum_univ_four, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h00 h01 h02 h20
  have h0 : c 0 = 0 := by linarith
  have h2 : c 2 = 0 := by linarith
  intro ν
  fin_cases ν
  · exact h0
  · exact h00
  · exact h2
  · exact h01

theorem solution (c : Fin 4 → ℝ) (h : ∑ ν, c ν • mgammaR ν = 0) : ∀ ν, c ν = 0 := indep_local c h

#print axioms solution

-- Prove2me | solution 1 for BookProof.ChapterE.exp_J_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:27:07.311296+00:00
-- url     : https://prove2.me/submissions/d5aa8233-e364-45aa-b096-20d5b76a7503

-- Generated from ChapterE.lean — solution of BookProof.ChapterE.exp_J_mulVec
import Mathlib
import Definitions.Def_ChapterE
import Theorems.Thm_BookProof_ChapterE_exp_J
open BookProof.ChapterE



open scoped Matrix BigOperators
open Filter
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) : (NormedSpace.exp (t • J)) *ᵥ ![1, 0] = Ψ t := by

  convert congr_arg ( fun m : Matrix ( Fin 2 ) ( Fin 2 ) ℝ => m *ᵥ ![1, 0] ) ( exp_J t ) using 1;
  ext i; fin_cases i <;> norm_num [ Ψ ] ;

-- Prove2me | solution 1 for BookProof.GaugeFixing.int_L_gf_evaluated
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T17:23:28.469362+00:00
-- url     : https://prove2.me/submissions/07d873f1-2904-4e88-a4a1-319bee5be311

-- Generated from ChapterGaugeFixing.lean — solution of BookProof.GaugeFixing.int_L_gf_evaluated
import Mathlib
import Definitions.Def_ChapterGaugeFixing
import Theorems.Thm_BookProof_GaugeFixing_L_gf_evaluation
import Theorems.Thm_BookProof_GaugeFixing_int_L_gf_eq_zero
open BookProof.GaugeFixing























variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

set_option maxHeartbeats 1000000 in
theorem solution (I : BrstIntegral S) :
    I.int (S.sub (2, 0) (S.mul (1, 0) (1, 0) S.B (gaugeField S))
      (S.mul (1, -1) (1, 1) S.c_bar S.c)) = 0 := by

  have h := int_L_gf_eq_zero S I
  rw [sTop, L_gf_evaluation] at h
  exact h

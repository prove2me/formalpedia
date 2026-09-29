-- Prove2me | solution 2 for BookProof.GaugeFixing.int_L_gf_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:27:42.681905+00:00
-- url     : https://prove2.me/submissions/a4ae99b3-ae82-424f-bad5-d7a3f4bf51e7

-- Generated from ChapterGaugeFixing.lean — solution of BookProof.GaugeFixing.int_L_gf_eq_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing























variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

set_option maxHeartbeats 1000000 in
theorem solution (I : BrstIntegral S) : I.int (sTop S (Psi S)) = 0 := I.int_of_s (Psi S)

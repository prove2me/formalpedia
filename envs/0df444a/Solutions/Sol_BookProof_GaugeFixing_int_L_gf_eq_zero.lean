-- Prove2me | solution 1 for BookProof.GaugeFixing.int_L_gf_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T14:45:31.133974+00:00
-- url     : https://prove2.me/submissions/dbca6730-1b22-49e8-9482-98199cf5c35a

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.int_L_gf_eq_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem solution (I : BrstIntegral S) : I.int (sTop S (Psi S)) = 0 :=
  I.int_of_s (Psi S)

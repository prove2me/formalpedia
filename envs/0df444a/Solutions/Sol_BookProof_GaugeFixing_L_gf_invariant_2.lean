-- Prove2me | solution 2 for BookProof.GaugeFixing.L_gf_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:19:31.831669+00:00
-- url     : https://prove2.me/submissions/84257ecf-4fb3-4173-a133-a1569ae2f000

-- Generated from ChapterGaugeFixing.lean — solution of BookProof.GaugeFixing.L_gf_invariant
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing























variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

set_option maxHeartbeats 1000000 in
theorem solution : S.s (S.s (Psi S)) = S.zero (2, 1) := S.s_nilpotent 2 (-1) (Psi S)

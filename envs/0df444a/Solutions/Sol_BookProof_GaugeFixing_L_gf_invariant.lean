-- Prove2me | solution 1 for BookProof.GaugeFixing.L_gf_invariant
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T14:45:48.83201+00:00
-- url     : https://prove2.me/submissions/3e14acca-9366-449f-8aad-64494fa0388a

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.L_gf_invariant
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem solution : S.s (S.s (Psi S)) = S.zero (2, 1) :=
  S.s_nilpotent 2 (-1) (Psi S)

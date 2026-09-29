-- Prove2me | solution 1 for BookProof.GaugeFixing.s_B_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T14:45:22.849168+00:00
-- url     : https://prove2.me/submissions/ed70826c-64e5-42ac-9e3d-a2b514fc23a7

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.s_B_eq_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem solution : S.s S.B = S.zero (1, 1) := by
  rw [← S.def_s_c_bar]
  exact S.s_nilpotent 1 (-1) S.c_bar

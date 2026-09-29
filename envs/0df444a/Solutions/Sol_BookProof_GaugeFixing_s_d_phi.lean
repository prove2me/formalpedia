-- Prove2me | solution 1 for BookProof.GaugeFixing.s_d_phi
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T14:45:17.491323+00:00
-- url     : https://prove2.me/submissions/970a2b6a-ac9c-45b6-8958-90c2aa89270c

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.s_d_phi
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem solution : S.s (S.d S.phi) = S.zero (1, 1) := by
  have h := S.sd_commute 0 0 S.phi
  rw [S.def_s_phi] at h
  rw [h]
  exact S.d_zero 0 1

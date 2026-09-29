-- Prove2me | solution 2 for BookProof.GaugeFixing.s_d_phi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:34:55.586718+00:00
-- url     : https://prove2.me/submissions/2b0310d9-2f5e-4ac7-b99a-2476f1330034

-- Generated from ChapterGaugeFixing.lean — solution of BookProof.GaugeFixing.s_d_phi
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing























variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

set_option maxHeartbeats 1000000 in
theorem solution : S.s (S.d S.phi) = S.zero (1, 1) := by

  have h : S.s (S.d S.phi) = S.d (S.s S.phi) := S.sd_commute 0 0 S.phi
  rw [S.def_s_phi] at h
  exact h.trans (S.d_zero 0 1)

-- Prove2me | solution 1 for FamousTheorems.beattyseq_symmdiff_beattyseq_pos
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:45.271483+00:00
-- url     : https://prove2.me/submissions/8ded8b52-8448-4c15-a99a-9a861de6d192

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {r s : ℝ}, 
    r.HolderConjugate s → 
    Irrational r → symmDiff {x | ∃ k > 0, beattySeq r k = x} {x | ∃ k > 0, beattySeq s k = x} = {n | 0 < n} :=
  @_root_.Irrational.beattySeq_symmDiff_beattySeq_pos

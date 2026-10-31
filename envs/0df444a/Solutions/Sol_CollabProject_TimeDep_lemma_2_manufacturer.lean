-- Prove2me | solution 1 for CollabProject.TimeDep.lemma_2_manufacturer
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:54:21.124665+00:00
-- url     : https://prove2.me/submissions/92ed049a-3b28-476f-8db2-96fd2ad04e40

import Mathlib
import Definitions.Def_CollabProject_TimeDep_Model
open CollabProject.TimeDep

theorem solution(S : SType) (M : MType)
    (h : Standing S M) :
    (M.s0 < M.p10 → ∀ a1 : Act, u0 M a1 .delay < u0 M a1 .keep) ∧
    (M.p20 < M.s0 → ∀ a1 : Act, u0 M a1 .keep < u0 M a1 .delay) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun hs a1 => ?_, fun hs a1 => ?_⟩ <;> cases a1 <;>
    simp [u0, penalty, delayCount, Act.delayPeriods] <;> linarith

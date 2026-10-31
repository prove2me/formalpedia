-- Prove2me | solution 1 for CollabProject.TimeDep.lemma_2_supplier
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:54:23.107696+00:00
-- url     : https://prove2.me/submissions/7f2b1694-1fb0-40f4-8414-caaa6ac1c1b5

import Mathlib
import Definitions.Def_CollabProject_TimeDep_Model
open CollabProject.TimeDep

theorem solution(S : SType)
    (hS : S.p11 < S.p21 ∧ S.p21 < S.s1) :
    ∀ (M : MType), Standing S M →
      ∀ (σ0 : Act → Act), (∀ a, IsBR0 M a (σ0 a)) →
        u1 S .keep (σ0 .keep) < u1 S .delay (σ0 .delay) := by
  intro M hM σ0 hbr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hM
  obtain ⟨hs1, hs2⟩ := hS
  have hk := hbr .keep
  have hd := hbr .delay
  simp only [IsBR0, SequentialGame.IsBR0] at hk hd
  have hk1 := hk .keep
  have hk2 := hk .delay
  have hd1 := hd .keep
  have hd2 := hd .delay
  cases hσk : σ0 Act.keep <;> cases hσd : σ0 Act.delay <;>
    simp only [hσk, hσd] at hk1 hk2 hd1 hd2 ⊢ <;>
    simp [u0, u1, penalty, delayCount, Act.delayPeriods] at hk1 hk2 hd1 hd2 ⊢ <;> linarith

-- Prove2me | solution 1 for Freiman.middle_cert_pair_binding
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T23:00:00.607754+00:00
-- url     : https://prove2.me/submissions/2b7fbf6d-eb35-4ef5-a15c-f3e46ecbbe6f

import Definitions.Def_Freiman_middleCertData
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open Freiman

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem solution :
    ∀ (C : MiddleCertCatalog) (p : MiddleCertPair), middleCertWitnessesValid C → middleCertPairValid C p 0 → certWitnessValid (middleCertPairWitness C p) := by
  intro C p hw hp
  rcases hp with ⟨hpos, hlen, hlo, hup, hfirst, hsecond, hdir, hstrict⟩
  have hi : p.witness - 1 < C.witnesses.length := by omega
  have hmem : middleCertWitness C p.witness ∈ C.witnesses := by
    simp only [middleCertWitness, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  have hv := hw _ hmem
  rcases hv with ⟨_, _, _, _, hl, hu, hv⟩
  rw [hdir] at hv
  simp only [ite_true] at hv hstrict
  rcases hv with ⟨_, heq, hbd⟩
  unfold certWitnessValid middleCertPairWitness
  dsimp
  refine ⟨hlo, hup, ?_, ?_, ?_, ?_, ?_, hbd, ?_⟩
  · norm_num [certRectangleValid, middleCertRectangle]
  · norm_num [middleCertRectangle]
  · simpa only [middleCertBound, hfirst] using hl
  · simpa only [middleCertBound, hsecond] using hu
  · funext i j
    simpa only [middleCertBound, hfirst, hsecond] using heq i j
  · rcases hstrict with h | h | h
    · left
      intro i j
      unfold middleCertWitnessLower
      positivity
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

#print axioms solution

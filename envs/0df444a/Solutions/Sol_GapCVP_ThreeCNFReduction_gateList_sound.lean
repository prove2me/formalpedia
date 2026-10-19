-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.gateList_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/692903c9-6410-4111-befb-02bd366da6e3

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_ThreeCNFReduction_orGate_satisfied

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.ThreeCNFReduction
open GapCVP.CL
namespace GapCVP.ThreeCNFReduction
theorem _root_.solution {T S : ℕ}
    (assignment : ℕ → Bool)
    (clauseIndex prefixIndex : ℕ)
    (literals : List (SignedLiteral T S))
    (hgates : satisfies assignment
      (gateList clauseIndex prefixIndex literals))
    (hstart : assignment
      (accumulatorVariable clauseIndex prefixIndex) = true)
    (hfinish : assignment
      (accumulatorVariable clauseIndex
        (prefixIndex + literals.length)) = false) :
    ∃ literal ∈ literals,
      assignment (sourceVariable literal.1) = literal.2 := by
  induction literals generalizing prefixIndex with
  | nil =>
    simp at hfinish
    simp [hstart] at hfinish
  | cons literal remaining ih =>
    simp only [gateList, satisfies_append] at hgates
    obtain ⟨hgate, hremaining⟩ := hgates
    have hchoice :=
      (orGate_satisfied assignment
        (sourceLiteral literal)
        (accumulatorLiteral clauseIndex (prefixIndex + 1) true)
        (accumulatorLiteral clauseIndex prefixIndex true)).mp hgate
    have houtput : literalSatisfied assignment
        (accumulatorLiteral clauseIndex prefixIndex true) := by
      simpa only [GapCVP.literalSatisfied, accumulatorLiteral, decide_eq_true_eq] using hstart
    rcases hchoice.mp houtput with hsatisfied | hnext
    · refine ⟨literal, by simp, ?_⟩
      simpa only [GapCVP.literalSatisfied, sourceLiteral, decide_eq_true_eq] using hsatisfied
    · have hnext' : assignment
          (accumulatorVariable clauseIndex (prefixIndex + 1)) = true := by
        simpa only [GapCVP.literalSatisfied, accumulatorLiteral, decide_eq_true_eq] using hnext
      have hindex :
          prefixIndex + 1 + remaining.length =
            prefixIndex + (literal :: remaining).length := by
        simp
        omega
      have hfinish' : assignment
          (accumulatorVariable clauseIndex
            (prefixIndex + 1 + remaining.length)) = false := by
        rw [hindex]
        exact hfinish
      obtain ⟨witness, hwitness, hvalue⟩ :=
        ih (prefixIndex + 1) hremaining hnext' hfinish'
      exact ⟨witness, by simp [hwitness], hvalue⟩
end GapCVP.ThreeCNFReduction

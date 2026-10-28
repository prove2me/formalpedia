-- Prove2me | solution 1 for BitDFT.shared_alphabet_sequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T22:25:16.572101+00:00
-- url     : https://prove2.me/submissions/0afbadb2-a6d2-4875-8663-d9397a8343c5

import Definitions.Def_BitDFT_SharedAlphabetComposition
import Theorems.Thm_BitDFT_machine_sequence_bound

set_option autoImplicit false
open IntMul BitDFT.SharedAlphabetComposition

/-- Sequentially run the child and multiplier stages, charging the single
    handoff transition and preserving the exact final configuration. -/
theorem solution (A M : MultitapeTM) (c : (leftStage A M).Cfg) (s u : ℕ)
    (hhalt : ((leftStage A M).step^[s] c).state = (leftStage A M).qHalt)
    (d : ((second A M).machine).Cfg)
    (hsecond : (second A M).machine.step^[u] (handoff A M ((leftStage A M).step^[s] c)) = d) :
    ∃ t : ℕ, t ≤ s + 1 + u ∧
      (program A M).machine.step^[t] (start A M c) = finish A M d := by
  obtain ⟨t,ht,he⟩ := BitDFT.machine_sequence_bound
    (first A M) (second A M) c s u hhalt
  refine ⟨t,ht,?_⟩
  change (second A M).machine.step^[u]
    (BitDFT.MachineSequence.handoff (first A M) (second A M)
      ((first A M).machine.step^[s] c)) = d at hsecond
  rw [hsecond] at he
  simpa [program,start,finish,handoff,first,second] using he

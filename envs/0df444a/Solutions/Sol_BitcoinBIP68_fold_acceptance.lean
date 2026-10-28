-- Prove2me | solution 1 for BitcoinBIP68.fold_acceptance
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T01:51:21.395243+00:00
-- url     : https://prove2.me/submissions/fd3f73c1-2b11-4bce-ac74-c4ef52356a04

import Definitions.Def_BIP68_Model
import Definitions.Def_BIP68_Core
import Theorems.Thm_BitcoinBIP68_decode_sequence

open BitcoinBIP68

/-- One fold step: evaluation of the new accumulator is evaluation of the old one together
with the declarative condition on the processed input. -/
private theorem step_iff (ctx : Context) (acc : Accumulator) (input : Input) :
    evaluate ctx (coreStep ctx acc input) = true ↔
      evaluate ctx acc = true ∧ inputSatisfied ctx input := by
  obtain ⟨hdis, htime, hdelay, hsec⟩ := BitcoinBIP68.decode_sequence input.sequence
  unfold coreStep evaluate inputSatisfied
  simp only [decide_eq_true_eq]
  cases hd : coreDisabled input.sequence with
  | true =>
    have : specDisabled input.sequence := hdis.1 hd
    simp only [ite_true]
    constructor
    · intro h; exact ⟨h, Or.inl this⟩
    · intro h; exact h.1
  | false =>
    have hnd : ¬ specDisabled input.sequence := fun h => by
      have := hdis.2 h; rw [hd] at this; exact Bool.false_ne_true this
    simp only [Bool.false_eq_true, ite_false]
    cases ht : coreTimeBased input.sequence with
    | true =>
      have hts : specTimeBased input.sequence := htime.1 ht
      simp only [ite_true, hts, hnd, false_or]
      rw [hsec]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, ?_⟩, ?_⟩ <;> omega
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, ?_⟩; omega
    | false =>
      have hts : ¬ specTimeBased input.sequence := fun h => by
        have := htime.2 h; rw [ht] at this; exact Bool.false_ne_true this
      simp only [Bool.false_eq_true, ite_false, hts, hnd, false_or]
      rw [hdelay]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨?_, h2⟩, ?_⟩ <;> omega
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨?_, h2⟩; omega

theorem solution (ctx : BitcoinBIP68.Context)
    (acc : BitcoinBIP68.Accumulator) (inputs : List BitcoinBIP68.Input) :
    BitcoinBIP68.evaluate ctx (inputs.foldl (BitcoinBIP68.coreStep ctx) acc) = true ↔
      BitcoinBIP68.evaluate ctx acc = true ∧
      ∀ input ∈ inputs, BitcoinBIP68.inputSatisfied ctx input := by
  induction inputs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, step_iff]
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

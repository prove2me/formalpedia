-- Prove2me | solution 1 for BitcoinBIP68.calculated_bounds
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T01:55:30.963238+00:00
-- url     : https://prove2.me/submissions/98abdf2c-50db-485c-94cd-e52b63c592ba

import Definitions.Def_BIP68_Model
import Definitions.Def_BIP68_Core
import Theorems.Thm_BitcoinBIP68_decode_sequence

open BitcoinBIP68

/-- The invariant carried through the fold. -/
private def inBounds (acc : Accumulator) : Prop :=
  (-1 ≤ acc.minHeight ∧ acc.minHeight ≤ (int32Max : Int)) ∧
  (-1 ≤ acc.minTime ∧ acc.minTime ≤ (int64Max : Int))

/-- Enforcement test: the Core Boolean agrees with the declarative predicate. -/
private theorem enabled_iff (version flags : BitVec 32) :
    coreEnabled version flags = true ↔ specEnabled version flags := by
  unfold coreEnabled specEnabled
  have h0 : (0 : BitVec 32).toNat = 0 := rfl
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  rw [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, BitVec.toNat_eq, BitVec.toNat_and,
    h0, h1, Nat.and_one_is_mod]
  constructor
  · rintro ⟨ha, hb⟩; exact ⟨ha, by omega⟩
  · rintro ⟨ha, hb⟩; exact ⟨ha, by omega⟩

/-- One step preserves the invariant, given the overflow bound for that input. -/
private theorem step_bounds (ctx : Context) (acc : Accumulator) (input : Input)
    (hacc : inBounds acc)
    (hsafe : ¬ specDisabled input.sequence →
      if specTimeBased input.sequence then
        ctx.mtp (input.coinHeight - 1) + 512 * specDelay input.sequence ≤ int64Max
      else input.coinHeight + specDelay input.sequence ≤ int32Max) :
    inBounds (coreStep ctx acc input) := by
  obtain ⟨hdis, htime, hdelay, hsec⟩ := BitcoinBIP68.decode_sequence input.sequence
  obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩ := hacc
  unfold coreStep inBounds
  cases hd : coreDisabled input.sequence with
  | true => simp only [ite_true]; exact ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩
  | false =>
    have hnd : ¬ specDisabled input.sequence := fun h => by
      have := hdis.2 h; rw [hd] at this; exact Bool.false_ne_true this
    have hs := hsafe hnd
    simp only [Bool.false_eq_true, ite_false]
    cases ht : coreTimeBased input.sequence with
    | true =>
      have hts : specTimeBased input.sequence := htime.1 ht
      rw [if_pos hts] at hs
      simp only [ite_true]
      rw [hsec]
      refine ⟨⟨ha1, ha2⟩, ?_, ?_⟩ <;> omega
    | false =>
      have hts : ¬ specTimeBased input.sequence := fun h => by
        have := htime.2 h; rw [ht] at this; exact Bool.false_ne_true this
      rw [if_neg hts] at hs
      simp only [Bool.false_eq_true, ite_false]
      rw [hdelay]
      refine ⟨⟨?_, ?_⟩, hb1, hb2⟩ <;> omega

private theorem fold_bounds (ctx : Context) (inputs : List Input) (acc : Accumulator)
    (hacc : inBounds acc)
    (hsafe : ∀ input ∈ inputs, ¬ specDisabled input.sequence →
      if specTimeBased input.sequence then
        ctx.mtp (input.coinHeight - 1) + 512 * specDelay input.sequence ≤ int64Max
      else input.coinHeight + specDelay input.sequence ≤ int32Max) :
    inBounds (inputs.foldl (coreStep ctx) acc) := by
  induction inputs generalizing acc with
  | nil => simpa using hacc
  | cons x xs ih =>
    rw [List.foldl_cons]
    apply ih
    · exact step_bounds ctx acc x hacc (hsafe x (List.mem_cons_self ..))
    · intro i hi; exact hsafe i (List.mem_cons_of_mem _ hi)

theorem solution (version flags : BitVec 32)
    (ctx : BitcoinBIP68.Context) (inputs : List BitcoinBIP68.Input)
    (hctx : BitcoinBIP68.admissible ctx inputs)
    (hsafe : BitcoinBIP68.noOverflow version flags ctx inputs) :
    let result := BitcoinBIP68.calculate version flags ctx inputs
    (-1 ≤ result.minHeight ∧ result.minHeight ≤ (BitcoinBIP68.int32Max : Int)) ∧
    (-1 ≤ result.minTime ∧ result.minTime ≤ (BitcoinBIP68.int64Max : Int)) := by
  intro result
  have hinit : inBounds initial := by
    simp only [inBounds, initial, int32Max, int64Max]
    omega
  show inBounds result
  unfold result calculate
  split
  · rename_i hen
    have hspec : specEnabled version flags := (enabled_iff version flags).1 hen
    apply fold_bounds ctx inputs initial hinit
    intro i hi hnd
    exact hsafe i hi hspec hnd
  · exact hinit

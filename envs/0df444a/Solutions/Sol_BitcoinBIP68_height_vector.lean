-- Prove2me | solution 1 for BitcoinBIP68.height_vector
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T01:55:30.325504+00:00
-- url     : https://prove2.me/submissions/0f594d50-3dec-4757-a9db-dbe7e7e00f4c

import Definitions.Def_BIP68_Model
import Definitions.Def_BIP68_Core
import Theorems.Thm_BitcoinBIP68_decode_sequence

open BitcoinBIP68

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

/-- The fold only ever prepends to the height list; the thresholds never touch it. -/
private theorem fold_heights (ctx : Context) (inputs : List Input) (acc : Accumulator) :
    (inputs.foldl (coreStep ctx) acc).heightsRev =
      (inputs.map fun input => if coreDisabled input.sequence then 0 else input.coinHeight).reverse
        ++ acc.heightsRev := by
  induction inputs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.reverse_cons, List.append_assoc]
    unfold coreStep
    split
    · simp [*]
    · split <;> simp [*]

theorem solution (version flags : BitVec 32)
    (ctx : BitcoinBIP68.Context) (inputs : List BitcoinBIP68.Input) :
    BitcoinBIP68.returnedHeights (BitcoinBIP68.calculate version flags ctx inputs) =
      BitcoinBIP68.expectedHeights version flags inputs := by
  unfold returnedHeights calculate expectedHeights
  by_cases hen : specEnabled version flags
  · have hcore : coreEnabled version flags = true := (enabled_iff version flags).2 hen
    rw [if_pos hcore, fold_heights]
    simp only [initial, List.append_nil, List.reverse_reverse]
    apply List.map_congr_left
    intro input _
    have hd := (BitcoinBIP68.decode_sequence input.sequence).1
    by_cases hdis : specDisabled input.sequence
    · have hb : coreDisabled input.sequence = true := hd.2 hdis
      have hp : specEnabled version flags ∧ specDisabled input.sequence := ⟨hen, hdis⟩
      rw [if_pos hb, if_pos hp]
    · have hb : ¬ (coreDisabled input.sequence = true) := fun h => hdis (hd.1 h)
      have hp : ¬ (specEnabled version flags ∧ specDisabled input.sequence) := fun h => hdis h.2
      rw [if_neg hb, if_neg hp]
  · have hcore : coreEnabled version flags = false := by
      cases h : coreEnabled version flags
      · rfl
      · exact absurd ((enabled_iff version flags).1 h) hen
    rw [if_neg (by simp [hcore])]
    simp only [List.reverse_reverse]
    apply List.map_congr_left
    intro input _
    have hp : ¬ (specEnabled version flags ∧ specDisabled input.sequence) := fun h => hen h.1
    rw [if_neg hp]

-- Prove2me | solution 1 for BitcoinBIP68.core_correct
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T01:55:31.720805+00:00
-- url     : https://prove2.me/submissions/90ca7404-b9a7-4d5b-828b-0daec731d8ab

import Definitions.Def_BIP68_Model
import Definitions.Def_BIP68_Core
import Theorems.Thm_BitcoinBIP68_fold_acceptance
import Theorems.Thm_BitcoinBIP68_height_vector

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

/-- The sentinel accumulator always evaluates to true. -/
private theorem evaluate_initial (ctx : Context) (hs : List Nat) :
    evaluate ctx { initial with heightsRev := hs } = true := by
  unfold evaluate initial
  simp only [decide_eq_true_eq]
  omega

theorem solution (version flags : BitVec 32)
    (ctx : BitcoinBIP68.Context) (inputs : List BitcoinBIP68.Input)
    (hctx : BitcoinBIP68.admissible ctx inputs)
    (hsafe : BitcoinBIP68.noOverflow version flags ctx inputs) :
    (BitcoinBIP68.sequenceLocks version flags ctx inputs = true ↔
      BitcoinBIP68.satisfiesBIP68 version flags ctx inputs) ∧
    BitcoinBIP68.returnedHeights (BitcoinBIP68.calculate version flags ctx inputs) =
      BitcoinBIP68.expectedHeights version flags inputs := by
  refine ⟨?_, BitcoinBIP68.height_vector version flags ctx inputs⟩
  unfold sequenceLocks calculate satisfiesBIP68
  split
  · rename_i hen
    have hspec : specEnabled version flags := (enabled_iff version flags).1 hen
    rw [BitcoinBIP68.fold_acceptance]
    have h0 : evaluate ctx initial = true := evaluate_initial ctx []
    constructor
    · rintro ⟨_, h⟩; exact Or.inr h
    · rintro (h | h)
      · exact absurd hspec h
      · exact ⟨h0, h⟩
  · rename_i hen
    have hspec : ¬ specEnabled version flags := fun h =>
      hen ((enabled_iff version flags).2 h)
    rw [evaluate_initial]
    simp only [true_iff]
    exact Or.inl hspec

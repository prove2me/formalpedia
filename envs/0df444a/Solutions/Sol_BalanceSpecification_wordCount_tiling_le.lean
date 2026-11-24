-- Prove2me | solution 1 for BalanceSpecification.wordCount_tiling_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:34.697084+00:00
-- url     : https://prove2.me/submissions/73e08fe3-6ef2-4b70-85a8-d048ac545c0a

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Theorems.Thm_BalanceSpecification_wordCount_le_boundary_mul_interior
public import Theorems.Thm_BalanceSpecification_wordCount_mul_le_pow
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.mem_wordFinset



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A]
namespace BalanceSpecification
theorem _root_.solution {L K : Set (Word A)} (hL : IsFactorial L) (M n k : ℕ)
    (hcore : ∀ w ∈ interiorLanguage L M, w.length = n → w ∈ K) :
    wordCount L (2 * M + k * n) ≤
      (Fintype.card A) ^ (2 * M) * (wordCount K n) ^ k := by
  have hmono : wordCount (interiorLanguage L M) n ≤ wordCount K n := by
    apply Finset.card_le_card
    intro w hw
    obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
    exact mem_wordFinset.mpr ⟨hcore w hwL hwlen, hwlen⟩
  calc
    wordCount L (2 * M + k * n) ≤ (Fintype.card A) ^ (2 * M) *
        wordCount (interiorLanguage L M) (k * n) :=
      wordCount_le_boundary_mul_interior L M (k * n)
    _ ≤ (Fintype.card A) ^ (2 * M) * (wordCount (interiorLanguage L M) n) ^ k :=
      Nat.mul_le_mul_left _ (wordCount_mul_le_pow (hL.interiorLanguage M) n k)
    _ ≤ (Fintype.card A) ^ (2 * M) * (wordCount K n) ^ k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmono k)
end BalanceSpecification

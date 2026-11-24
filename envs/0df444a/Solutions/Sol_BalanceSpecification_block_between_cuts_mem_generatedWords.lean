-- Prove2me | solution 1 for BalanceSpecification.block_between_cuts_mem_generatedWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:10.792262+00:00
-- url     : https://prove2.me/submissions/6df23f38-645c-41e9-9797-99925fa33f1b

module
public import Definitions.Def_BalanceSpecificaton_Coded
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Theorems.Thm_BalanceSpecification_append_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_block_append
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_generatedWords_of_mem
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution {C : Set (Word A)}
    {x : Configuration A} {p : ℤ → ℤ} (hp : StrictMono p)
    (hwords : ∀ i : ℤ, block x (p i) ((p (i + 1) - p i).toNat) ∈ C)
    (i : ℤ) (n : ℕ) :
    block x (p i) ((p (i + n) - p i).toNat) ∈ generatedWords C := by
  induction n with
  | zero =>
    simpa only [Nat.cast_zero, add_zero, sub_self, Int.toNat_zero,
      block, List.ofFn_zero] using nil_mem_generatedWords C
  | succ n ih =>
    have hleft : p i ≤ p (i + n) := hp.monotone (by omega)
    have hright : p (i + n) ≤ p (i + n + 1) := hp.monotone (by omega)
    have hlen : (p (i + (n + 1 : ℕ)) - p i).toNat =
        (p (i + n) - p i).toNat + (p (i + n + 1) - p (i + n)).toNat := by
      have h1 := Int.toNat_of_nonneg (sub_nonneg.mpr hleft)
      have h2 := Int.toNat_of_nonneg (sub_nonneg.mpr hright)
      have h3 := Int.toNat_of_nonneg (sub_nonneg.mpr (hleft.trans hright))
      simp only [Nat.cast_add, Nat.cast_one, add_assoc] at h1 h2 h3 ⊢
      omega
    rw [hlen, block_append]
    have hstart : p i + ((p (i + n) - p i).toNat : ℤ) = p (i + n) := by
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hleft)]
      omega
    rw [hstart]
    exact append_mem_generatedWords ih (mem_generatedWords_of_mem (hwords (i + n)))
end BalanceSpecification

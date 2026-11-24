-- Prove2me | solution 1 for BalanceSpecification.strictMono_int_cofinal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:09.308937+00:00
-- url     : https://prove2.me/submissions/cb085036-061c-43fd-8684-91bef8121731

module
public import Definitions.Def_BalanceSpecificaton_Coded
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
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
theorem _root_.solution {p : ℤ → ℤ} (hp : StrictMono p) (k : ℤ) :
    (∃ i, p i ≤ k) ∧ (∃ j, k ≤ p j) := by
  have hstep (i : ℤ) : p i + 1 ≤ p (i + 1) := by
    have hlt := hp (show i < i + 1 by omega)
    omega
  have hpos (n : ℕ) : p 0 + (n : ℤ) ≤ p (n : ℤ) := by
    induction n with
    | zero => simp only [Nat.cast_zero, add_zero, le_refl]
    | succ n ih =>
      have hs := hstep (n : ℤ)
      simp only [Nat.cast_add, Nat.cast_one] at hs ⊢
      omega
  have hneg (n : ℕ) : p (-(n : ℤ)) ≤ p 0 - n := by
    induction n with
    | zero => simp only [Nat.cast_zero, neg_zero, sub_zero, le_refl]
    | succ n ih =>
      have hs := hstep (-((n + 1 : ℕ) : ℤ))
      have he : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by omega
      rw [he] at hs
      simp only [Nat.cast_add, Nat.cast_one] at hs ⊢
      omega
  constructor
  · refine ⟨-((p 0 - k).natAbs : ℤ), ?_⟩
    have hbound : p 0 - k ≤ ((p 0 - k).natAbs : ℤ) := Int.le_natAbs
    exact (hneg (p 0 - k).natAbs).trans (by omega)
  · refine ⟨((k - p 0).natAbs : ℤ), ?_⟩
    have hbound : k - p 0 ≤ ((k - p 0).natAbs : ℤ) := Int.le_natAbs
    exact (show k ≤ p 0 + ((k - p 0).natAbs : ℤ) by omega).trans
      (hpos (k - p 0).natAbs)
end BalanceSpecification

-- Prove2me | solution 1 for BalanceSpecification.IsConcatenation.block_infix_generatedWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:22:11.871+00:00
-- url     : https://prove2.me/submissions/44754e38-1dfa-4952-ac1c-2f32e5181d41

module
public import Definitions.Def_BalanceSpecificaton_Coded
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Theorems.Thm_BalanceSpecification_strictMono_int_cofinal
public import Theorems.Thm_BalanceSpecification_block_between_cuts_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_block_append


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
namespace IsConcatenation
theorem _root_.solution {C : Set (Word A)}
    {x : Configuration A} (hx : IsConcatenation C x) (k : ℤ) (n : ℕ) :
    ∃ v ∈ generatedWords C, block x k n <:+: v := by
  obtain ⟨p, hp, hwords⟩ := hx
  obtain ⟨i, hi⟩ := (strictMono_int_cofinal hp k).1
  obtain ⟨j, hj⟩ := (strictMono_int_cofinal hp (k + n)).2
  have hij : i ≤ j := hp.le_iff_le.mp (by omega)
  have hdiff : i + ((j - i).toNat : ℤ) = j := by
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hij)]
    omega
  have hv := block_between_cuts_mem_generatedWords hp hwords i (j - i).toNat
  rw [hdiff] at hv
  refine ⟨block x (p i) ((p j - p i).toNat), hv, ?_⟩
  let a := (k - p i).toNat
  let b := (p j - (k + n)).toNat
  have ha : (a : ℤ) = k - p i := Int.toNat_of_nonneg (by omega)
  have hb : (b : ℤ) = p j - (k + n) := Int.toNat_of_nonneg (by omega)
  have hlen : (p j - p i).toNat = a + n + b := by omega
  have hstart : p i + (a : ℤ) = k := by omega
  refine ⟨block x (p i) a, block x (p i + (a + n : ℕ)) b, ?_⟩
  symm
  rw [hlen, block_append, block_append, hstart]
end IsConcatenation
end BalanceSpecification

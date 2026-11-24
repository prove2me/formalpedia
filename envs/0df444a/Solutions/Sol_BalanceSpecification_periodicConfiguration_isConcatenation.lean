-- Prove2me | solution 1 for BalanceSpecification.periodicConfiguration_isConcatenation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:55:56.060984+00:00
-- url     : https://prove2.me/submissions/50fb1f14-f965-4390-98dc-538e0762f5d6

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Topology.Continuous
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Coded
public import Theorems.Thm_BalanceSpecification_block_periodicConfiguration

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution {C : Set (Word A)}
    {w : Word A} (hwC : w ∈ C) (hw : 0 < w.length) :
    IsConcatenation C (periodicConfiguration w hw) := by
  refine ⟨fun j => j * w.length, ?_, ?_⟩
  · intro a b hab
    exact mul_lt_mul_of_pos_right hab (Nat.cast_pos.mpr hw)
  · intro j
    have hdiff : (j + 1) * (w.length : ℤ) - j * w.length = w.length := by ring
    rw [hdiff, Int.toNat_natCast, block_periodicConfiguration]
    exact hwC
end BalanceSpecification

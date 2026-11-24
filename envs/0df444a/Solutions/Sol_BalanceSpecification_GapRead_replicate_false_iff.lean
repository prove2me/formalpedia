-- Prove2me | solution 1 for BalanceSpecification.GapRead.replicate_false_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:43:11.8758+00:00
-- url     : https://prove2.me/submissions/8b32af45-8827-48a2-a186-4e970632f581

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
public import Theorems.Thm_BalanceSpecification_GapRead_replicate_false

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
open BalanceSpecification.GapRead
variable {S : Set ℕ} {a b c : ℕ} {u v : Word Bool}
namespace BalanceSpecification.GapRead
theorem _root_.solution {n : ℕ} :
    GapRead S a (List.replicate n false) b ↔ a = b + n := by
  induction n generalizing a with
  | zero =>
    constructor
    · intro h
      cases h
      rfl
    · intro h
      subst a
      exact .nil b
  | succ n ih =>
    constructor
    · intro h
      cases h with
      | zero h => have h' := ih.mp h; omega
    · intro h
      have he : a = (b + n) + 1 := by omega
      rw [he, List.replicate_succ]
      exact .zero (replicate_false b n)
end BalanceSpecification.GapRead

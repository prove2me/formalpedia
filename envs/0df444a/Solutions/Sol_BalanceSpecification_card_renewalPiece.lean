-- Prove2me | solution 1 for BalanceSpecification.card_renewalPiece
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:40.563109+00:00
-- url     : https://prove2.me/submissions/0149f0d0-d976-4a39-8f45-5341a0bd4c1d

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapRenewal

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution (S : Set ℕ) (n s : ℕ) :
    (renewalPiece S n s).card = renewalCount S (n - s - 1) := by
  classical
  unfold renewalPiece renewalCount
  exact Finset.card_image_of_injective _ (fun _ _ h => (List.append_right_inj _).mp h)
end BalanceSpecification

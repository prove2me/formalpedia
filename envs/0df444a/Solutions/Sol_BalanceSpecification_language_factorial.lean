-- Prove2me | solution 1 for BalanceSpecification.language_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:34:14.297579+00:00
-- url     : https://prove2.me/submissions/b6abd340-3d69-4490-98f6-057d0ced2152

module
public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Language
public import Theorems.Thm_BalanceSpecification_block_subword

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {A : Type*} [TopologicalSpace A] (X : ShiftSpace A) :
    IsFactorial (language X) := by
  rintro u v ⟨p, q, rfl⟩ ⟨x, hx, k, hk⟩
  exact ⟨x, hx, k + p.length, block_subword x k p u q hk⟩
end BalanceSpecification

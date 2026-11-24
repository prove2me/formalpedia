-- Prove2me | solution 1 for BalanceSpecification.mem_forbiddenShift_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:34:20.956628+00:00
-- url     : https://prove2.me/submissions/f14fc14d-29b7-4398-8887-d67da85f5ef0

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Forbidden

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
namespace BalanceSpecification
theorem _root_.solution {F : Set (Word A)} {x : Configuration A} :
    x ∈ (forbiddenShift F).carrier ↔ ∀ w ∈ F, ∀ k : ℤ, block x k w.length ≠ w :=
  Iff.rfl
end BalanceSpecification

-- Prove2me | solution 1 for BalanceSpecification.mem_extensionPairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:32:10.494802+00:00
-- url     : https://prove2.me/submissions/e811fbe5-e56e-4002-93a5-0e99f6f7391e

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution {u p s : Word A} {a b : ℕ} :
    (⟨p, s⟩ : (_ : Word A) × Word A) ∈ extensionPairs L u a b ↔
      p ∈ predecessorFinset L u a ∧ s ∈ followerFinset L (p ++ u) b := by
  classical
  exact Finset.mem_sigma
end BalanceSpecification

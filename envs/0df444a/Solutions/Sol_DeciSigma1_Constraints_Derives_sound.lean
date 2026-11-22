-- Prove2me | solution 1 for DeciSigma1.Constraints.Derives.sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:20:21.409203+00:00
-- url     : https://prove2.me/submissions/fe47ac30-e030-408f-b989-f64f2a3224b9

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Theorems.Thm_DeciSigma1_Semantics_Tree_node_le_node_iff
attribute [local simp] DeciSigma1.Semantics.Tree.node_le_node_iff



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Constraints
namespace Derives
theorem _root_.solution {Γ : List (LitT n V)} {x y : V} (h : Derives Γ x y) :
    ∀ ρ, Covariant.Sat ρ Γ → ρ x ≤ ρ y := by
  induction h with
  | refl x => exact fun _ _ => le_rfl
  | lit hl => exact fun _ hρ => hρ _ hl
  | trans _ _ ih₁ ih₂ => exact fun ρ hρ => le_trans (ih₁ ρ hρ) (ih₂ ρ hρ)
  | decomp i hl _ hu ih =>
    intro ρ hρ
    exact (Tree.node_le_node_iff ..).mp
      (le_trans (le_trans (hρ _ hl) (ih ρ hρ)) (hρ _ hu)) i
end Derives
end DeciSigma1.Constraints

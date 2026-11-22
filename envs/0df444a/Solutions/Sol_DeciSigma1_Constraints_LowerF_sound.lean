-- Prove2me | solution 1 for DeciSigma1.Constraints.LowerF.sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:21:29.639804+00:00
-- url     : https://prove2.me/submissions/1e7d489e-6c46-4535-b27b-c47581a103de

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Theorems.Thm_DeciSigma1_Constraints_Derives_sound
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_bot_iff
attribute [local simp] DeciSigma1.Semantics.Tree.le_bot_iff



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Constraints
namespace LowerF
theorem _root_.solution {Γ : List (LitT n V)} {x : V} {ρ : V → Semantics.Tree n}
    (h : LowerF Γ x) (hρ : Covariant.Sat ρ Γ) : (ρ x).fn [] ≠ some Sym.bot := by
  obtain ⟨a, u, hl, hd⟩ := h
  intro hx
  have hle : Semantics.Tree.node (ρ ∘ a) ≤ ρ x := le_trans (hρ _ hl) (hd.sound ρ hρ)
  rw [(Tree.root_eq_bot_iff _).mp hx] at hle
  exact Tree.node_ne_bot _ ((Tree.le_bot_iff _).mp hle)
end LowerF
end DeciSigma1.Constraints

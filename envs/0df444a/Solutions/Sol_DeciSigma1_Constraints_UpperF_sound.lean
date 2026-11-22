-- Prove2me | solution 1 for DeciSigma1.Constraints.UpperF.sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:23:02.9318+00:00
-- url     : https://prove2.me/submissions/229ad460-1638-465e-9e89-ffc8f2c034aa

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Theorems.Thm_DeciSigma1_Constraints_Derives_sound
public import Theorems.Thm_DeciSigma1_Constraints_LowerF_sound
public import Theorems.Thm_DeciSigma1_Constraints_LowerTop_sound
public import Theorems.Thm_DeciSigma1_Semantics_Tree_top_le_iff
attribute [local simp] DeciSigma1.Semantics.Tree.top_le_iff



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Constraints
namespace UpperF
theorem _root_.solution {Γ : List (LitT n V)} {x : V} {ρ : V → Semantics.Tree n}
    (h : UpperF Γ x) (hρ : Covariant.Sat ρ Γ) : (ρ x).fn [] ≠ some Sym.top := by
  obtain ⟨v, b, hu, hd⟩ := h
  intro hx
  have hle : ρ x ≤ Semantics.Tree.node (ρ ∘ b) := le_trans (hd.sound ρ hρ) (hρ _ hu)
  rw [(Tree.root_eq_top_iff _).mp hx] at hle
  exact Tree.node_ne_top _ ((Tree.top_le_iff _).mp hle)
end UpperF
end DeciSigma1.Constraints

-- Prove2me | solution 1 for DeciSigma1.Constraints.LowerTop.sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:22:16.841912+00:00
-- url     : https://prove2.me/submissions/b2d40d52-f27e-4794-afc2-b3e4769b93f0

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Theorems.Thm_DeciSigma1_Constraints_Derives_sound
public import Theorems.Thm_DeciSigma1_Constraints_LowerF_sound
public import Theorems.Thm_DeciSigma1_Semantics_Tree_top_le_iff
attribute [local simp] DeciSigma1.Semantics.Tree.top_le_iff



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Constraints
namespace LowerTop
theorem _root_.solution {Γ : List (LitT n V)} {x : V} {ρ : V → Semantics.Tree n}
    (h : LowerTop Γ x) (hρ : Covariant.Sat ρ Γ) : ρ x = Tree.top := by
  obtain ⟨u, hl, hd⟩ := h
  have hle := hd.sound ρ hρ
  have hu : ρ u = Tree.top := hρ _ hl
  rw [hu] at hle
  exact (Tree.top_le_iff _).mp hle
end LowerTop
end DeciSigma1.Constraints

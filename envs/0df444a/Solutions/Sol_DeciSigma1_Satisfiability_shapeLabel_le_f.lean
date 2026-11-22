-- Prove2me | solution 1 for DeciSigma1.Satisfiability.shapeLabel_le_f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:28:17.433311+00:00
-- url     : https://prove2.me/submissions/3ece4a04-bee4-41b4-8b29-4d52a9517c01

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Theorems.Thm_DeciSigma1_Satisfiability_shapeLabel_eq_f_iff
public import Theorems.Thm_DeciSigma1_Satisfiability_shapeLabel_eq_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_bot_le
attribute [local simp] DeciSigma1.Semantics.Tree.bot_le



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Satisfiability
theorem _root_.solution {π : List (Fin n)} {x : V}
    (h : UpperLabel Γ π .f x) : shapeLabel Γ x π ≤ Sym.f := by
  classical
  by_cases hl : LowerLabel Γ π .f x
  · rw [shapeLabel_eq_f_iff.mpr ⟨hl, h⟩]
  · rw [shapeLabel_eq_bot_iff.mpr ⟨hl, Or.inr h⟩]
    exact Sym.bot_le _
end DeciSigma1.Satisfiability

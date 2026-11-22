-- Prove2me | solution 1 for DeciSigma1.Satisfiability.f_le_shapeLabel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:32:45.862254+00:00
-- url     : https://prove2.me/submissions/d0f06310-104d-4f55-9c33-5016f6060be7

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Theorems.Thm_DeciSigma1_Satisfiability_shapeLabel_eq_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_top
attribute [local simp] DeciSigma1.Semantics.Tree.le_top



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Satisfiability
theorem _root_.solution {π : List (Fin n)} {x : V}
    (h : LowerLabel Γ π .f x) : Sym.f ≤ shapeLabel Γ x π := by
  cases he : shapeLabel Γ x π with
  | bot => exact False.elim ((shapeLabel_eq_bot_iff.mp he).1 h)
  | f => exact le_rfl
  | top => exact Sym.le_top _
end DeciSigma1.Satisfiability

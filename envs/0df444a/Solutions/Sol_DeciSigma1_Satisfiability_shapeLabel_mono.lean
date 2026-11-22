-- Prove2me | solution 1 for DeciSigma1.Satisfiability.shapeLabel_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:29:25.831819+00:00
-- url     : https://prove2.me/submissions/f92e7ac1-6085-48cf-96c3-821d76b31363

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Theorems.Thm_DeciSigma1_Satisfiability_shapeLabel_eq_f_iff
public import Theorems.Thm_DeciSigma1_Satisfiability_shapeLabel_eq_bot_iff
public import Theorems.Thm_DeciSigma1_Satisfiability_shapeLabel_le_f
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_top
attribute [local simp] DeciSigma1.Semantics.Tree.le_top



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Satisfiability
theorem _root_.solution {π τ : List (Fin n)} {x y : V}
    (hl : LowerLabel Γ π .f x → LowerLabel Γ τ .f y)
    (hu : ∀ g, UpperLabel Γ τ g y → UpperLabel Γ π g x) :
    shapeLabel Γ x π ≤ shapeLabel Γ y τ := by
  cases he : shapeLabel Γ y τ with
  | top => exact Sym.le_top _
  | f => exact shapeLabel_le_f (hu .f (shapeLabel_eq_f_iff.mp he).2)
  | bot =>
    obtain ⟨hn, hb | hf⟩ := shapeLabel_eq_bot_iff.mp he
    · rw [shapeLabel_eq_bot_iff.mpr ⟨fun hx => hn (hl hx), Or.inl (hu .bot hb)⟩]
    · rw [shapeLabel_eq_bot_iff.mpr ⟨fun hx => hn (hl hx), Or.inr (hu .f hf)⟩]
end DeciSigma1.Satisfiability

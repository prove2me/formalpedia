-- Prove2me | solution 1 for DeciSigma1.Logic.ConjunctiveClause.extend_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:52:49.28609+00:00
-- url     : https://prove2.me/submissions/3a95644c-2325-4d05-ab53-a87f8dc2ac28

module
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Syntax
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Flatten

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Logic
variable {T : Type → Type} {D V : Type} {I : Interpretation T D}
open DeciSigma1.Logic.ConjunctiveClause
variable (F : Flattening I) {m : ℕ} (c : ConjunctiveClause T (Fin m))
namespace DeciSigma1.Logic.ConjunctiveClause
theorem _root_.solution {C : D → Prop} (hC : I.TermClosed C) {ρ : Fin m → D} (hρ : ∀ v, C (ρ v)) :
    ∀ w, C (c.extend F ρ w)
  | .inl v => hρ v
  | .inr _ => hC ρ _ hρ
end DeciSigma1.Logic.ConjunctiveClause

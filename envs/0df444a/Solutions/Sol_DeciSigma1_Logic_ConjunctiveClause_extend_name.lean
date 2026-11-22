-- Prove2me | solution 1 for DeciSigma1.Logic.ConjunctiveClause.extend_name
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:50.815322+00:00
-- url     : https://prove2.me/submissions/422357ba-ca37-40d8-95b2-5b673fed0e14

module
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Syntax
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Flatten
public import Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_holds_append
attribute [local simp] DeciSigma1.Logic.ConjunctiveClause.holds_append

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Logic
variable {T : Type → Type} {D V : Type} {I : Interpretation T D}
open DeciSigma1.Logic.ConjunctiveClause
variable (F : Flattening I) {m : ℕ} (c : ConjunctiveClause T (Fin m))
variable [DecidableEq (T (Fin m))]
namespace DeciSigma1.Logic.ConjunctiveClause
theorem _root_.solution (ρ : Fin m → D) {t : T (Fin m)} (ht : t ∈ c.terms F) :
    c.extend F ρ (c.name F t) = I.eval ρ t := by
  simp [extend, name, List.getElem?_idxOf, ht]
end DeciSigma1.Logic.ConjunctiveClause

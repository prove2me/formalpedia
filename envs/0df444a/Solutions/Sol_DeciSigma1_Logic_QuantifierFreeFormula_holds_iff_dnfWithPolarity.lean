-- Prove2me | solution 1 for DeciSigma1.Logic.QuantifierFreeFormula.holds_iff_dnfWithPolarity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:53:08.017948+00:00
-- url     : https://prove2.me/submissions/39b04c24-a57a-4dc8-b9e0-d9690b0dfb31

module
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Syntax
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Flatten
public import Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_holds_append
public import Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_exists_holds_cross
attribute [local simp] DeciSigma1.Logic.ConjunctiveClause.holds_append

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Logic
variable {T : Type → Type} {D V : Type} {I : Interpretation T D}
namespace DeciSigma1.Logic
namespace QuantifierFreeFormula
theorem _root_.solution (φ : QuantifierFreeFormula T V) (ρ : V → D)
    (b : Bool) :
    (if b then φ.Holds I ρ else ¬ φ.Holds I ρ) ↔ ∃ c ∈ φ.dnfWithPolarity b, c.Holds I ρ := by
  induction φ generalizing b with
  | le s t => cases b <;> simp [dnfWithPolarity, Holds, ConjunctiveClause.Holds]
  | tt => cases b <;> simp [dnfWithPolarity, Holds, ConjunctiveClause.Holds]
  | ff => cases b <;> simp [dnfWithPolarity, Holds, ConjunctiveClause.Holds]
  | not φ ih =>
    cases b
    · simpa [dnfWithPolarity, Holds] using ih true
    · simpa [dnfWithPolarity, Holds] using ih false
  | and φ ψ ihφ ihψ =>
    cases b <;> simp [dnfWithPolarity, Holds, ConjunctiveClause.exists_holds_cross, or_and_right,
      exists_or, ← ihφ, ← ihψ]
    tauto
  | or φ ψ ihφ ihψ =>
    cases b <;> simp [dnfWithPolarity, Holds, ConjunctiveClause.exists_holds_cross, or_and_right,
      exists_or, ← ihφ, ← ihψ]
end QuantifierFreeFormula
end DeciSigma1.Logic

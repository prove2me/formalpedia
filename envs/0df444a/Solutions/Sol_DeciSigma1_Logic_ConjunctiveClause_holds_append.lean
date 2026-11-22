-- Prove2me | solution 1 for DeciSigma1.Logic.ConjunctiveClause.holds_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:34:25.171879+00:00
-- url     : https://prove2.me/submissions/64160ca2-7bc7-40b0-8f6c-b55b086ff7c8

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
namespace DeciSigma1.Logic
namespace ConjunctiveClause
theorem _root_.solution (ρ : V → D) (c d : ConjunctiveClause T V) :
    (c.append d).Holds I ρ ↔ c.Holds I ρ ∧ d.Holds I ρ := by
  simp only [Holds, append, List.mem_append, or_imp, forall_and]
  tauto
end ConjunctiveClause
end DeciSigma1.Logic

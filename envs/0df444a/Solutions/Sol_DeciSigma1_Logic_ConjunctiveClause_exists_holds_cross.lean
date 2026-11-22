-- Prove2me | solution 1 for DeciSigma1.Logic.ConjunctiveClause.exists_holds_cross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:52:44.331008+00:00
-- url     : https://prove2.me/submissions/5a0e1238-1bd5-404b-b616-847daf0f7b42

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
namespace DeciSigma1.Logic
namespace ConjunctiveClause
theorem _root_.solution (ρ : V → D) (cs ds : List (ConjunctiveClause T V)) :
    (∃ c ∈ cross cs ds, c.Holds I ρ) ↔ (∃ c ∈ cs, c.Holds I ρ) ∧ (∃ d ∈ ds, d.Holds I ρ) := by
  simp only [cross, List.mem_flatMap, List.mem_map]
  aesop
end ConjunctiveClause
end DeciSigma1.Logic

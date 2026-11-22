-- Prove2me | solution 1 for DeciSigma1.Logic.ConjunctiveClause.mem_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:42.901834+00:00
-- url     : https://prove2.me/submissions/25e03b2d-f573-4ec9-a2a0-2bed8b5be329

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
namespace DeciSigma1.Logic.ConjunctiveClause
theorem _root_.solution {p : T (Fin m) × T (Fin m)} (hp : p ∈ c.positive ∨ p ∈ c.negative) :
    p.1 ∈ c.terms F ∧ p.2 ∈ c.terms F := by
  constructor <;> refine List.mem_flatMap.mpr ⟨p, List.mem_append.mpr hp, ?_⟩ <;>
    simp [F.mem_subterms]
end DeciSigma1.Logic.ConjunctiveClause

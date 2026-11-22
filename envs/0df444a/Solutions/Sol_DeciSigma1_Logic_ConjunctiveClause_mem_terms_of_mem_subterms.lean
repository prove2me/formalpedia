-- Prove2me | solution 1 for DeciSigma1.Logic.ConjunctiveClause.mem_terms_of_mem_subterms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:46.113281+00:00
-- url     : https://prove2.me/submissions/49339891-7410-47c2-8854-412517fc0fb4

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
theorem _root_.solution {s t : T (Fin m)} (ht : t ∈ c.terms F)
    (hs : s ∈ F.subterms t) : s ∈ c.terms F := by
  obtain ⟨p, hp, ht⟩ := List.mem_flatMap.mp ht
  refine List.mem_flatMap.mpr ⟨p, hp, ?_⟩
  rcases List.mem_append.mp ht with ht | ht
  · exact List.mem_append_left _ (F.subterms_trans ht hs)
  · exact List.mem_append_right _ (F.subterms_trans ht hs)
end DeciSigma1.Logic.ConjunctiveClause

-- Prove2me | solution 1 for DeciSigma1.Logic.ConjunctiveClause.eq_eval_of_holds_constraints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:53:14.799533+00:00
-- url     : https://prove2.me/submissions/83d87883-ccf7-40be-adfb-7cc284c30c9e

module
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Syntax
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Flatten
public import Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_mem_terms_of_mem_subterms

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Logic
variable {T : Type → Type} {D V : Type} {I : Interpretation T D}
open DeciSigma1.Logic.ConjunctiveClause
variable (F : Flattening I) {m : ℕ} (c : ConjunctiveClause T (Fin m))
variable [DecidableEq (T (Fin m))]
namespace DeciSigma1.Logic.ConjunctiveClause
theorem _root_.solution {σ : c.Names F → D}
    (hσ : ∀ l ∈ c.constraints F, F.Holds σ l) {t : T (Fin m)} (ht : t ∈ c.terms F) :
    σ (c.name F t) = I.eval (σ ∘ .inl) t :=
  F.eval_of_holds_defs _ _ σ t fun s hs l hl =>
    hσ l (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨s, c.mem_terms_of_mem_subterms F ht hs, hl⟩))
end DeciSigma1.Logic.ConjunctiveClause

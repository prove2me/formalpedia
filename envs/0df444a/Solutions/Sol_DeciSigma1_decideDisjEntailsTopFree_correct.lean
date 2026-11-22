-- Prove2me | solution 1 for DeciSigma1.decideDisjEntailsTopFree_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:29:24.107095+00:00
-- url     : https://prove2.me/submissions/9e5e343f-2de4-46a4-8b5c-a8efe9e31765

module
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ElementaryBound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedForm
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Main

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
variable {n : ℕ} {V : Type}
variable [Fintype V] [DecidableEq V] {k : ℕ}
namespace DeciSigma1
theorem _root_.solution (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsTopFree Γ q) = true ↔ DisjEntailsTopFree Γ q :=
  @decide_eq_true_iff _ (decideDisjEntailsTopFree Γ q)
end DeciSigma1

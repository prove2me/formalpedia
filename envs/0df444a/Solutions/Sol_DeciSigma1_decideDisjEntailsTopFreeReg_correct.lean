-- Prove2me | solution 1 for DeciSigma1.decideDisjEntailsTopFreeReg_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:29:49.540807+00:00
-- url     : https://prove2.me/submissions/3cb35a5d-fb70-4aba-b23a-c68712b2cdd5

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
    @decide _ (decideDisjEntailsTopFreeReg Γ q) = true ↔ DisjEntailsTopFreeReg Γ q :=
  @decide_eq_true_iff _ (decideDisjEntailsTopFreeReg Γ q)
end DeciSigma1

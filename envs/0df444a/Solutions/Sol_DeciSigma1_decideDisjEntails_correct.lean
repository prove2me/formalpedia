-- Prove2me | solution 1 for DeciSigma1.decideDisjEntails_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:28:36.963427+00:00
-- url     : https://prove2.me/submissions/0d737b73-c8c0-419c-b5ac-f28dbcf2a1d9

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
variable {n k : ℕ} {V : Type}
variable [Fintype V] [DecidableEq V]
namespace DeciSigma1
theorem _root_.solution (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : @decide _ (decideDisjEntails c Γ q) = true ↔ DisjEntails c Γ q :=
  @decide_eq_true_iff _ (decideDisjEntails c Γ q)
end DeciSigma1

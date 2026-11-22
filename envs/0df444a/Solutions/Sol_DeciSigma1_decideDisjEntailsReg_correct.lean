-- Prove2me | solution 1 for DeciSigma1.decideDisjEntailsReg_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:29:06.24915+00:00
-- url     : https://prove2.me/submissions/b791331f-ddb3-44f0-9dc4-480b64b95e07

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
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsReg c Γ q) = true ↔ DisjEntailsReg c Γ q :=
  @decide_eq_true_iff _ (decideDisjEntailsReg c Γ q)
end DeciSigma1

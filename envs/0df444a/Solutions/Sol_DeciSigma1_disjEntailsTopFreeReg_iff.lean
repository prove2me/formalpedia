-- Prove2me | solution 1 for DeciSigma1.disjEntailsTopFreeReg_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:31:04.095103+00:00
-- url     : https://prove2.me/submissions/fa6d79cd-9743-44ca-831f-ff2446a49857

module
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ElementaryBound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedForm
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Theorems.Thm_DeciSigma1_Entailment_disjEntailsIn_regular_iff


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
variable {n : ℕ} {V : Type}
variable [Fintype V] [DecidableEq V] {k : ℕ}
omit [DecidableEq V]
omit [Fintype V]
namespace DeciSigma1
theorem _root_.solution [Finite V] (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : DisjEntailsTopFreeReg Γ q ↔ DisjEntailsTopFree Γ q := by
  classical
  let := Fintype.ofFinite V
  exact Entailment.disjEntailsIn_regular_iff Γ q
end DeciSigma1

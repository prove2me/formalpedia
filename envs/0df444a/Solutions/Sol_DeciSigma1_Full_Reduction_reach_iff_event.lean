-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.reach_iff_event
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:21:29.378795+00:00
-- url     : https://prove2.me/submissions/12adfbeb-0ced-4da1-b1e6-26c2e82aa1a1

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Theorems.Thm_DeciSigma1_Full_Closure_reach_iff_cuts_of_not_hasUnaryObstruction


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Constraints DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Automata
variable {n : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Reduction
theorem _root_.solution (a b : Closure.Config n V)
    (ha : ¬ HasUnaryObstruction c Γ (a.1, a.2.1) a.2.2) :
    Reach c Γ a b ↔ Event c Γ a b :=
  reach_iff_cuts_of_not_hasUnaryObstruction (q := (b.1, b.2.1)) (t := b.2.2) ha
end DeciSigma1.Full.Reduction

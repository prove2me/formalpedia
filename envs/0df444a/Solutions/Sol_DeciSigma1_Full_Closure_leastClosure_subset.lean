-- Prove2me | solution 1 for DeciSigma1.Full.Closure.leastClosure_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:41:28.175426+00:00
-- url     : https://prove2.me/submissions/f43d7aef-0617-497b-973e-f4fae0d33601

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Theorems.Thm_DeciSigma1_Full_Closure_hull_least

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Closure
theorem _root_.solution {S : Set (Config n V)} (hS : IsSolution c Γ S) : leastClosure c Γ ⊆ S :=
  hull_least hS.closed hS.facts (Set.empty_subset _)
end DeciSigma1.Full.Closure

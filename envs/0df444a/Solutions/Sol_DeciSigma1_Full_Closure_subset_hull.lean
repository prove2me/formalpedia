-- Prove2me | solution 1 for DeciSigma1.Full.Closure.subset_hull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:40:27.295376+00:00
-- url     : https://prove2.me/submissions/e63b8f81-19b9-4c26-967e-f99d0f3821a2

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Semantics
open DeciSigma1.Constraints
variable {n : ℕ}
variable {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Closure
theorem _root_.solution (A : Set (Config n V)) : A ⊆ hull c Γ A :=
  fun p hp => ⟨p, Or.inr hp, .refl⟩
end DeciSigma1.Full.Closure

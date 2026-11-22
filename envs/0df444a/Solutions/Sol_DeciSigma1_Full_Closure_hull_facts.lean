-- Prove2me | solution 1 for DeciSigma1.Full.Closure.hull_facts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:39:04.356421+00:00
-- url     : https://prove2.me/submissions/a8f6848a-9090-4892-b8be-45b530fcee0f

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
theorem _root_.solution (A : Set (Config n V)) {p : Config n V} (hp : Fact Γ p) :
    p ∈ hull c Γ A := ⟨p, Or.inl hp, .refl⟩
end DeciSigma1.Full.Closure

-- Prove2me | solution 1 for DeciSigma1.Full.Closure.hull_least
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:40:29.027696+00:00
-- url     : https://prove2.me/submissions/dfd0238b-6ec1-4b29-a737-003d2cf167fb

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Theorems.Thm_DeciSigma1_Full_Closure_Reach_mem_of_closed

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Semantics
open DeciSigma1.Constraints
variable {n : ℕ}
variable {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Closure
theorem _root_.solution {A S : Set (Config n V)} (hc : Closed c Γ S)
    (hf : ∀ ⦃p⦄, Fact Γ p → p ∈ S) (ha : A ⊆ S) : hull c Γ A ⊆ S := by
  rintro b ⟨a, hf' | ha', hr⟩
  · exact hr.mem_of_closed hc (hf hf')
  · exact hr.mem_of_closed hc (ha ha')
end DeciSigma1.Full.Closure

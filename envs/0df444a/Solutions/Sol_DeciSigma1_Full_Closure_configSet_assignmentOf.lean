-- Prove2me | solution 1 for DeciSigma1.Full.Closure.configSet_assignmentOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:38:20.866809+00:00
-- url     : https://prove2.me/submissions/482e68d7-baa2-4374-9aae-0e501da5794d

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
theorem _root_.solution (S : Set (Config n V))
    (hc : Closed c Γ S) (hd : Consistent S) :
    configSet c (assignmentOf S hc hd) = S := by
  ext ⟨v, s, w⟩
  exact Set.ext_iff.mp (leaf_decode c _ s) w
end DeciSigma1.Full.Closure

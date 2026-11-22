-- Prove2me | solution 1 for DeciSigma1.Full.Closure.hull_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:39:03.752682+00:00
-- url     : https://prove2.me/submissions/3d64003d-2aae-4b60-a2f2-dc1395054ff5

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
theorem _root_.solution (A : Set (Config n V)) : Closed c Γ (hull c Γ A) := by
  rintro a b h ⟨s, hs, hr⟩
  exact ⟨s, hs, .tail hr h⟩
end DeciSigma1.Full.Closure

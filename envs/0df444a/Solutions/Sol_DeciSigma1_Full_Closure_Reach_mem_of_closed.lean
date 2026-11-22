-- Prove2me | solution 1 for DeciSigma1.Full.Closure.Reach.mem_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:39:02.978817+00:00
-- url     : https://prove2.me/submissions/017ae2cf-f280-4018-b69a-018758cfd4a3

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
namespace Reach
theorem _root_.solution {a b : Config n V} {S : Set (Config n V)}
    (h : Reach c Γ a b) (hc : Closed c Γ S) (ha : a ∈ S) : b ∈ S := by
  induction h with
  | refl => exact ha
  | tail _ hs ih => exact hc hs ih
end Reach
end DeciSigma1.Full.Closure

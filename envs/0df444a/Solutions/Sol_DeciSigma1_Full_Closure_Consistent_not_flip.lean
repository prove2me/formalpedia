-- Prove2me | solution 1 for DeciSigma1.Full.Closure.Consistent.not_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:40:55.351556+00:00
-- url     : https://prove2.me/submissions/12a93bfd-b067-4b1b-a2cd-1e6a2ab51a92

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Closure
namespace Consistent
theorem _root_.solution {S : Set (Config n V)} (hc : Consistent S)
    {v : V} {s : Bool} {w : List (Fin n)} (hp : (v, s, w) ∈ S) : (v, !s, w) ∉ S := by
  intro hm
  cases s with
  | false => exact hc (.pair v w) hp hm
  | true => exact hc (.pair v w) hm hp
end Consistent
end DeciSigma1.Full.Closure

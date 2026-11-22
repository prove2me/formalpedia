-- Prove2me | solution 1 for DeciSigma1.Full.Closure.moves_reach
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:40:39.187047+00:00
-- url     : https://prove2.me/submissions/fb91670b-a7c4-40e3-99aa-619fc1bac0f3

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
theorem _root_.solution {a b : Config n V} (h : Moves c Γ a b) : Reach c Γ a b := by
  induction h with
  | refl => exact .refl
  | tail _ hm ih => exact .tail ih (.move hm)
end DeciSigma1.Full.Closure

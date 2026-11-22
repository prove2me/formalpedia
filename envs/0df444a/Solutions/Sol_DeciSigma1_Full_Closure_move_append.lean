-- Prove2me | solution 1 for DeciSigma1.Full.Closure.move_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:41:44.547522+00:00
-- url     : https://prove2.me/submissions/24effa99-aeb5-4cee-9cda-3705dd16d1cb

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
theorem _root_.solution (σ : List (Fin n)) {p q : Config n V} (h : Move c Γ p q) :
    Move c Γ (p.1, p.2.1, p.2.2 ++ σ) (q.1, q.2.1, q.2.2 ++ σ) := by
  cases h with
  | copyPlus hl => exact .copyPlus hl
  | copyMinus hl => exact .copyMinus hl
  | fLePush i hl => exact .fLePush i hl
  | fLePop i hl => exact .fLePop i hl
  | leFPop i hl => exact .leFPop i hl
  | leFPush i hl => exact .leFPush i hl
end DeciSigma1.Full.Closure

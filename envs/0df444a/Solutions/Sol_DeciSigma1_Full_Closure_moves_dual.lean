-- Prove2me | solution 1 for DeciSigma1.Full.Closure.moves_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:42:39.151716+00:00
-- url     : https://prove2.me/submissions/55289dc9-c3bf-4ec6-bd57-9ce434291224

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Theorems.Thm_DeciSigma1_Full_Closure_move_dual

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Closure
theorem _root_.solution {p q : Config n V} (h : Moves c Γ p q) :
    Moves c Γ (flipC q) (flipC p) := by
  induction h with
  | refl => exact .refl
  | tail _ hm ih => exact ih.head (move_dual hm)
end DeciSigma1.Full.Closure

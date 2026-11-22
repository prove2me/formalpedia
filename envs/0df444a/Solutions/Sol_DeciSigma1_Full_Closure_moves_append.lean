-- Prove2me | solution 1 for DeciSigma1.Full.Closure.moves_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:42:40.869028+00:00
-- url     : https://prove2.me/submissions/f6cca66a-905c-4ba8-ae8b-2252c99221ed

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Theorems.Thm_DeciSigma1_Full_Closure_move_append

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Closure
theorem _root_.solution (σ : List (Fin n)) {p q : Config n V} (h : Moves c Γ p q) :
    Moves c Γ (p.1, p.2.1, p.2.2 ++ σ) (q.1, q.2.1, q.2.2 ++ σ) := by
  induction h with
  | refl => exact .refl
  | tail _ hm ih => exact ih.tail (move_append σ hm)
end DeciSigma1.Full.Closure

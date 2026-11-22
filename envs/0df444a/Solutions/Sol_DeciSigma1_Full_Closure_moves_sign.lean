-- Prove2me | solution 1 for DeciSigma1.Full.Closure.moves_sign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:14:34.93857+00:00
-- url     : https://prove2.me/submissions/175f0f4c-9813-4d44-8ade-37d23919cd73

module
public import Mathlib.Data.Fintype.Powerset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Theorems.Thm_DeciSigma1_Full_Closure_move_sign

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Closure
theorem _root_.solution {p q : Config n V}
    (h : Relation.ReflTransGen (Move c Γ) p q) :
    Bool.xor q.2.1 (polarity c q.2.2) =
      Bool.xor p.2.1 (polarity c p.2.2) := by
  induction h with
  | refl => rfl
  | tail _ hm ih => exact (move_sign hm).trans ih
end DeciSigma1.Full.Closure

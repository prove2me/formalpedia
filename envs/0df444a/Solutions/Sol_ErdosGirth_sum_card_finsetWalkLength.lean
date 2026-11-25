-- Prove2me | solution 1 for ErdosGirth.sum_card_finsetWalkLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:29:49.55597+00:00
-- url     : https://prove2.me/submissions/ecce3b82-171a-476e-b409-1fdbb8d8368f

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) (u : V) :
    ∑ v, #(G.finsetWalkLength n u v) ≤ Fintype.card V ^ n := by
  induction n generalizing u with
  | zero =>
    simp only [finsetWalkLength, pow_zero]
    rw [sum_eq_single u]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  | succ n ih =>
    calc ∑ v, #(G.finsetWalkLength (n + 1) u v)
        ≤ ∑ v, ∑ w : G.neighborSet u, #(G.finsetWalkLength n w v) := by
          refine sum_le_sum fun v _ => ?_
          refine (card_biUnion_le).trans ?_
          simp
      _ = ∑ w : G.neighborSet u, ∑ v, #(G.finsetWalkLength n w v) := sum_comm
      _ ≤ ∑ _w : G.neighborSet u, Fintype.card V ^ n := sum_le_sum fun w _ => ih w
      _ ≤ Fintype.card V ^ (n + 1) := by
          rw [sum_const, card_univ, smul_eq_mul, pow_succ, mul_comm]
          exact Nat.mul_le_mul_left _ (Fintype.card_subtype_le _)
end ErdosGirth

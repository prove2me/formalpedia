-- Prove2me | solution 1 for ErdosGirth.sum_card_closed_walks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:30:36.549227+00:00
-- url     : https://prove2.me/submissions/a87d7a46-d63c-4fae-987f-faff7585ed72

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
public import Theorems.Thm_ErdosGirth_sum_card_finsetWalkLength

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) :
    ∑ u, #(G.finsetWalkLength (n + 1) u u) ≤ Fintype.card V ^ (n + 1) := by
  calc ∑ u, #(G.finsetWalkLength (n + 1) u u)
      ≤ ∑ u, ∑ w : G.neighborSet u, #(G.finsetWalkLength n w u) := by
        refine sum_le_sum fun v _ => ?_
        refine (card_biUnion_le).trans ?_
        simp
    _ ≤ ∑ u, ∑ w, #(G.finsetWalkLength n w u) := by
        refine sum_le_sum fun u _ => ?_
        exact (sum_map univ (Function.Embedding.subtype _)
          (fun w => #(G.finsetWalkLength n w u))).symm.le.trans
          (sum_le_sum_of_subset (subset_univ _))
    _ = ∑ w, ∑ u, #(G.finsetWalkLength n w u) := sum_comm
    _ ≤ ∑ _w : V, Fintype.card V ^ n := sum_le_sum fun w _ => sum_card_finsetWalkLength G n w
    _ = Fintype.card V ^ (n + 1) := by
        rw [sum_const, card_univ, smul_eq_mul, pow_succ, mul_comm]
end ErdosGirth

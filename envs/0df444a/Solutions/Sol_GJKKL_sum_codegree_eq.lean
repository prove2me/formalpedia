-- Prove2me | solution 1 for GJKKL.sum_codegree_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:41.648647+00:00
-- url     : https://prove2.me/submissions/6369c135-efa4-4652-b246-1908582a6551

module
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_VertexCount

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) (v : V) :
    ∑ u ∈ univ.erase v, codegree H v u = ∑ e ∈ H.filter (fun e => v ∈ e), (e.erase v).card := by
  simp only [codegree, card_filter]
  rw [sum_comm]
  rw [sum_filter]
  refine sum_congr rfl fun e _ => ?_
  by_cases hv : v ∈ e
  · rw [if_pos hv, ← card_filter]
    congr 1
    ext u
    simp only [mem_filter, mem_erase, mem_univ, and_true]
    tauto
  · rw [if_neg hv]
    exact sum_eq_zero fun u _ => by simp [hv]
end GJKKL

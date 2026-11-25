-- Prove2me | solution 1 for ErdosPosa.moore_no_same_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:23:41.316745+00:00
-- url     : https://prove2.me/submissions/d9c647b9-d676-4959-84b0-cadd430c770e

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Definitions.Def_ErdosPosaLib_EPMoore
public import Theorems.Thm_ErdosPosa_dist_lt_of_mem_support
public import Theorems.Thm_ErdosPosa_ncard_support_le
public import Theorems.Thm_ErdosPosa_cyc_of_walk
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*} {H : SimpleGraph V}
namespace ErdosPosa
theorem _root_.solution {r : ℕ} (hno : ∀ S : Set V, S.ncard ≤ 2 * r + 1 → ¬ Cyc H S)
    {v x y : V} {d : ℕ} (hd : d ≤ r) (hx : H.Reachable v x) (hxd : H.dist v x = d)
    (hy : H.Reachable v y) (hyd : H.dist v y = d) (a : H.Adj x y) : False := by
  obtain ⟨qx, hqx⟩ := hx.exists_walk_length_eq_dist
  obtain ⟨qy, hqy⟩ := hy.exists_walk_length_eq_dist
  let W : H.Walk x y := qx.reverse.append qy
  apply hno {z | z ∈ W.support}
  · refine (ncard_support_le W).trans ?_
    simp only [W, Walk.length_append, Walk.length_reverse]
    omega
  refine cyc_of_walk a W (fun y hy => hy) ?_
  simp only [W, Walk.edges_append, Walk.edges_reverse, List.mem_append, List.mem_reverse, not_or]
  refine ⟨?_, ?_⟩
  · intro h
    have := dist_lt_of_mem_support qx hqx (qx.snd_mem_support_of_mem_edges h) a.ne.symm
    omega
  · intro h
    have := dist_lt_of_mem_support qy hqy (qy.fst_mem_support_of_mem_edges h) a.ne
    omega
end ErdosPosa

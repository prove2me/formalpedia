-- Prove2me | solution 1 for ErdosPosa.moore_parent_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:23:38.940921+00:00
-- url     : https://prove2.me/submissions/720c0e6f-7d65-4ca3-abed-71abcfac9e42

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Definitions.Def_ErdosPosaLib_EPMoore
public import Theorems.Thm_ErdosPosa_dist_le_of_mem_support
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
    {v x p1 p2 : V} {d : ℕ} (hd : d + 1 ≤ r) (h1 : H.Reachable v p1) (h1d : H.dist v p1 = d)
    (h2 : H.Reachable v p2) (h2d : H.dist v p2 = d) (hx : H.dist v x = d + 1)
    (a1 : H.Adj x p1) (a2 : H.Adj x p2) : p1 = p2 := by
  by_contra hne
  obtain ⟨q1, hq1⟩ := h1.exists_walk_length_eq_dist
  obtain ⟨q2, hq2⟩ := h2.exists_walk_length_eq_dist
  let W : H.Walk x p1 := Walk.cons a2 (q2.reverse.append q1)
  apply hno {y | y ∈ W.support}
  · refine (ncard_support_le W).trans ?_
    simp only [W, Walk.length_cons, Walk.length_append, Walk.length_reverse]
    omega
  refine cyc_of_walk a1 W (fun y hy => hy) ?_
  simp only [W, Walk.edges_cons, Walk.edges_append, Walk.edges_reverse, List.mem_cons,
    List.mem_append, List.mem_reverse, not_or]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hne
    rw [Sym2.eq_iff] at h
    rcases h with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact absurd h.symm a1.ne
  · intro h
    have := dist_le_of_mem_support q2 hq2 (q2.fst_mem_support_of_mem_edges h)
    omega
  · intro h
    have := dist_le_of_mem_support q1 hq1 (q1.fst_mem_support_of_mem_edges h)
    omega
end ErdosPosa

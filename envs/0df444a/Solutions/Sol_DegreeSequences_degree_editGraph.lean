-- Prove2me | solution 1 for DegreeSequences.degree_editGraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:18:42.24414+00:00
-- url     : https://prove2.me/submissions/080e1bd7-37f5-44e2-b6dc-b1ef8201e9fd

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
public import Theorems.Thm_DegreeSequences_degree_eq_sum_ite
public import Theorems.Thm_DegreeSequences_sum_ite_mem_finset

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (R A : Finset (Sym2 V)) [DecidableRel (editGraph G R A).Adj]
    (hR : ∀ e ∈ R, e ∈ G.edgeSet) (hA : ∀ e ∈ A, e ∉ G.edgeSet ∧ ¬ e.IsDiag) (v : V) :
    (editGraph G R A).degree v + ∑ e ∈ R, (if v ∈ e then 1 else 0) =
      G.degree v + ∑ e ∈ A, (if v ∈ e then 1 else 0) := by
  rw [← sum_ite_mem_finset v R (fun e he => G.not_isDiag_of_mem_edgeSet (hR e he)),
    ← sum_ite_mem_finset v A (fun e he => (hA e he).2), degree_eq_sum_ite, degree_eq_sum_ite,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h1 : s(v, w) ∈ R → G.Adj v w := fun h => hR _ h
  have h2 : s(v, w) ∈ A → ¬ G.Adj v w ∧ v ≠ w := fun h =>
    ⟨(hA _ h).1, by simpa using (hA _ h).2⟩
  have h3 : G.Adj v w → v ≠ w := G.ne_of_adj
  simp only [editGraph]
  by_cases a : G.Adj v w <;> by_cases b : s(v, w) ∈ R <;> by_cases c : s(v, w) ∈ A <;>
    by_cases d : v = w <;> simp_all
end DegreeSequences

-- Prove2me | solution 1 for DeletionCode.BipartiteSelection.exists_independent_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:59.752048+00:00
-- url     : https://prove2.me/submissions/e63b6175-12e7-42e2-8806-5a924a92f05c

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_BipartiteSelection
import Theorems.Thm_DeletionCode_BipartiteSelection_exists_large_label_fiber
import Theorems.Thm_DeletionCode_BipartiteSelection_good_color_valid
import Theorems.Thm_DeletionCode_BipartiteSelection_mem_goodVertices
attribute [local simp] DeletionCode.BipartiteSelection.mem_goodVertices

set_option autoImplicit true
open DeletionCode DeletionCode.BipartiteSelection
open SimpleGraph
open scoped BigOperators
variable {V : Type*} (G : SimpleGraph V)
variable [Fintype V]
namespace DeletionCode.BipartiteSelection
theorem _root_.solution :
    ∃ I : Finset V, (∀ v ∈ I, Good G v) ∧ G.IsIndepSet (I : Set V) ∧
      (goodVertices G).card ≤ 2 * I.card := by
  classical
  obtain ⟨a, ha⟩ := exists_large_label_fiber (goodVertices G) (color G) (by decide)
  refine ⟨(goodVertices G).filter (fun v => color G v = a), ?_, ?_, ha⟩
  · intro v hv
    exact (mem_goodVertices G v).mp (Finset.mem_filter.mp hv).1
  · intro v hv w hw _ hvw
    have hv' := Finset.mem_filter.mp hv
    have hw' := Finset.mem_filter.mp hw
    exact good_color_valid G ((mem_goodVertices G v).mp hv'.1) hvw
      (hv'.2.trans hw'.2.symm)
end DeletionCode.BipartiteSelection

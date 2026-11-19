-- Prove2me | solution 1 for DeletionCode.BipartiteSelection.exists_large_label_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:47:56.782925+00:00
-- url     : https://prove2.me/submissions/e7a3f226-549d-459d-80f9-83f11803e2e5

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_BipartiteSelection

set_option autoImplicit true
open DeletionCode DeletionCode.BipartiteSelection
open SimpleGraph
open scoped BigOperators
namespace DeletionCode.BipartiteSelection
theorem _root_.solution {V : Type*} {Q : ℕ} (I : Finset V)
    (label : V → Fin Q) (hQ : 1 ≤ Q) :
    ∃ a : Fin Q, I.card ≤ Q * (I.filter (fun v => label v = a)).card := by
  classical
  have hne : (Finset.univ : Finset (Fin Q)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin Q))
    (fun b => (I.filter (fun v => label v = b)).card) hne
  refine ⟨a, ?_⟩
  calc
    I.card = ∑ b : Fin Q, (I.filter (fun v => label v = b)).card := by
      symm
      simpa only [Finset.mem_univ, Finset.filter_true] using
        Finset.sum_card_fiberwise_eq_card_filter I (Finset.univ : Finset (Fin Q)) label
    _ ≤ ∑ _b : Fin Q, (I.filter (fun v => label v = a)).card :=
      Finset.sum_le_sum (fun b hb => ha b hb)
    _ = _ := by simp
end DeletionCode.BipartiteSelection

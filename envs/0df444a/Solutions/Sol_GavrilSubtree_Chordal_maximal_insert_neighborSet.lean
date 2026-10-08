-- Prove2me | solution 1 for GavrilSubtree.Chordal.maximal_insert_neighborSet
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:16:38.731259+00:00
-- url     : https://prove2.me/submissions/33f02cfc-d577-4a41-ac4c-5a3b81d890fa

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting



namespace GavrilSubtree.Chordal

universe u

theorem mi_core {V : Type u} (G : SimpleGraph V) (v : V)
    (hv : IsSimplicial G v) : Maximal G.IsClique (insert v (G.neighborSet v)) := by
  have hc : G.IsClique (insert v (G.neighborSet v)) := by
    rw [SimpleGraph.isClique_insert]
    exact ⟨hv, fun b hb _ => ((G.mem_neighborSet _ _).mp hb)⟩
  refine ⟨hc, fun t ht hle => ?_⟩
  intro x hx
  by_cases hxv : x = v
  · subst hxv; exact Set.mem_insert _ _
  · right
    have := ht (hle (Set.mem_insert v _)) hx (Ne.symm hxv)
    exact (G.mem_neighborSet _ _).mpr this

end GavrilSubtree.Chordal

open GavrilSubtree.Chordal


universe u

theorem solution {V : Type u} (G : SimpleGraph V) (v : V)
    (hv : IsSimplicial G v) : Maximal G.IsClique (insert v (G.neighborSet v)) := by
  exact mi_core G v hv

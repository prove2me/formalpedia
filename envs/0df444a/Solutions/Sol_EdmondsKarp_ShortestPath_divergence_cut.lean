-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.divergence_cut
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:35:57.425772+00:00
-- url     : https://prove2.me/submissions/db3f0a40-5502-485b-a7e9-31f3c3fd3b77

import Mathlib

theorem solution {V : Type} [Fintype V] [DecidableEq V] (d : V → V → ℝ) (S : Finset V) :
    (∑ u ∈ S, ∑ v : V, (d u v - d v u)) =
      ∑ u ∈ S, ∑ v ∈ Sᶜ, (d u v - d v u) := by
  have hsplit (u : V) : (∑ v : V, (d u v - d v u)) =
      (∑ v ∈ S, (d u v - d v u)) + (∑ v ∈ Sᶜ, (d u v - d v u)) := by
    exact (Finset.sum_add_sum_compl S (fun v => d u v - d v u)).symm
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have hz : (∑ u ∈ S, ∑ v ∈ S, (d u v - d v u)) = 0 := by
    simp only [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (Finset.sum_comm)
  rw [hz, zero_add]

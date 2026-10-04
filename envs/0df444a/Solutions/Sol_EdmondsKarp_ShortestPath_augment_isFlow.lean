-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.augment_isFlow
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T20:09:49.890172+00:00
-- url     : https://prove2.me/submissions/16d7b5d2-db14-4b2d-b9ed-e50b12ec36f0

import Theorems.Thm_EdmondsKarp_ShortestPath_augment_bounds
import Theorems.Thm_EdmondsKarp_ShortestPath_augment_net_change
import Theorems.Thm_EdmondsKarp_ShortestPath_pathArcs_incidence
import Theorems.Thm_EdmondsKarp_ShortestPath_network_divergence
import Theorems.Thm_EdmondsKarp_ShortestPath_pathEps_bounds

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hf : IsFlow N f) (hP : IsAugPath N f P) :
    0 < pathEps N f P ∧ IsFlow N (augment N f P) ∧
    augment N f P N.t N.s = f N.t N.s + pathEps N f P := by
  obtain ⟨hb, hret⟩ := augment_bounds N f P hf hP
  have heps := (pathEps_bounds N f P hf hP).1
  refine ⟨heps, ⟨?_, ?_, ?_⟩, hret⟩
  · intro u v h
    rcases Finset.mem_insert.mp h with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [hret]
      exact add_nonneg (hf.1 _ _ (Finset.mem_insert_self _ _)) heps.le
    · exact (hb u v h).1
  · intro u v h
    exact (hb u v h).2
  · intro u
    have hdelta := Finset.sum_congr (s₁ := Finset.univ) (by rfl)
      (fun v (_ : v ∈ (Finset.univ : Finset V)) => augment_net_change N f P hP u v)
    have hi (a b : ℝ) (q : Prop) [Decidable q] :
        (if q then a - b else 0) = (if q then a else 0) - (if q then b else 0) := by
      split_ifs <;> simp
    simp_rw [hi] at hdelta
    simp only [Finset.sum_sub_distrib] at hdelta
    have hp := pathArcs_incidence P hP.1 u (pathEps N f P)
    rw [hP.2.1, hP.2.2.1] at hp
    rw [hp] at hdelta
    have hbal := hf.2.2 u
    rw [network_divergence] at hbal
    rw [network_divergence, hret]
    by_cases hs : u = N.s <;> by_cases ht : u = N.t <;>
      simp only [hs, ht, eq_comm, N.source_ne_sink, ↓reduceIte, Option.some.injEq] at hdelta hbal ⊢ <;>
      linarith

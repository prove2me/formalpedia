-- Prove2me | solution 1 for EdmondsKarp.MaxCapacity.cut_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:02:23.190952+00:00
-- url     : https://prove2.me/submissions/e5976fe8-65b4-42ea-a0f1-fa37f6ed60c6

import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation
import Definitions.Def_EdmondsKarp_MaxCapacity_Run

namespace EdmondsKarp.MaxCapacity

theorem aux_cb_netflow {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (X : Finset V) (hs : N.s ∈ X) (ht : N.t ∉ X)
    (f : V → V → ℝ) (hf : IsFlow N f) :
    cutFlowOut N f X - cutFlowIn N f X = f N.t N.s := by
  obtain ⟨_, _, hcons⟩ := hf
  set a : V × V → ℝ := fun p => if p ∈ N.arcs then f p.1 p.2 else 0 with ha
  have hout : ∀ u, (∑ v ∈ Finset.univ.filter (fun v => (u, v) ∈ N.arcs), f u v)
      = ∑ v, a (u, v) := by
    intro u; rw [Finset.sum_filter]
  have hin : ∀ u, (∑ v ∈ Finset.univ.filter (fun v => (v, u) ∈ N.arcs), f v u)
      = ∑ v, a (v, u) := by
    intro u; rw [Finset.sum_filter]
  have hsum : ∑ u ∈ X, (∑ v, a (u, v) - ∑ v, a (v, u)) = 0 := by
    apply Finset.sum_eq_zero; intro u _; rw [← hout, ← hin]; exact hcons u
  have e1 : ∑ u ∈ X, ∑ v, a (u, v) = ∑ p : V × V, (if p.1 ∈ X then a p else 0) := by
    rw [← Finset.sum_filter]
    have : (Finset.univ.filter (fun p : V × V => p.1 ∈ X)) = X ×ˢ Finset.univ := by
      ext p; simp
    rw [this, Finset.sum_product]
  have e2 : ∑ u ∈ X, ∑ v, a (v, u) = ∑ p : V × V, (if p.2 ∈ X then a p else 0) := by
    rw [← Finset.sum_filter]
    have : (Finset.univ.filter (fun p : V × V => p.2 ∈ X)) = Finset.univ ×ˢ X := by
      ext p; simp
    rw [this, Finset.sum_product, Finset.sum_comm]
  rw [Finset.sum_sub_distrib, e1, e2, ← Finset.sum_sub_distrib] at hsum
  have hpt : ∀ p : V × V, ((if p.1 ∈ X then a p else 0) - (if p.2 ∈ X then a p else 0))
      = (if p ∈ N.A.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X) then f p.1 p.2 else 0)
        - (if p ∈ insert (N.t, N.s) (N.A.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X))
            then f p.1 p.2 else 0) := by
    rintro ⟨x, y⟩
    simp only [ha, Network.arcs, Finset.mem_insert, Finset.mem_filter, Prod.mk.injEq]
    by_cases hx : x ∈ X <;> by_cases hy : y ∈ X
    · have h1 : ¬ (x = N.t ∧ y = N.s) := fun h => ht (h.1 ▸ hx)
      simp [hx, hy, h1]
    · have h1 : ¬ (x = N.t ∧ y = N.s) := fun h => ht (h.1 ▸ hx)
      simp [hx, hy, h1]
    · simp [hx, hy]
    · have h1 : ¬ (x = N.t ∧ y = N.s) := fun h => hy (h.2 ▸ hs)
      simp [hx, hy, h1]
  simp_rw [hpt] at hsum
  rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem] at hsum
  simp only [Finset.univ_inter] at hsum
  have hnotin : (N.t, N.s) ∉ N.A.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X) := by
    intro h; exact N.return_not_mem (Finset.mem_filter.1 h).1
  rw [Finset.sum_insert hnotin] at hsum
  unfold cutFlowOut cutFlowIn
  linarith

theorem aux_cb_le {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (X : Finset V) (f : V → V → ℝ) (hf : IsFlow N f) :
    cutFlowOut N f X - cutFlowIn N f X ≤ cutCap N X := by
  obtain ⟨hnn, hle, _⟩ := hf
  have h1 : cutFlowOut N f X ≤ cutCap N X := by
    unfold cutFlowOut cutCap
    apply Finset.sum_le_sum
    intro p hp
    exact hle p.1 p.2 (Finset.mem_filter.1 hp).1
  have h2 : 0 ≤ cutFlowIn N f X := by
    unfold cutFlowIn
    apply Finset.sum_nonneg
    intro p hp
    exact hnn p.1 p.2 (Finset.mem_insert_of_mem (Finset.mem_filter.1 hp).1)
  linarith

end EdmondsKarp.MaxCapacity

open EdmondsKarp.MaxCapacity

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (hcap : IntegralCaps N) (X : Finset V) (hs : N.s ∈ X) (ht : N.t ∉ X)
    (f : V → V → ℝ) (hf : IsFlow N f) :
    cutFlowOut N f X - cutFlowIn N f X = f N.t N.s ∧
      cutFlowOut N f X - cutFlowIn N f X ≤ cutCap N X :=
  ⟨aux_cb_netflow N X hs ht f hf, aux_cb_le N X f hf⟩

-- Prove2me | solution 1 for DirKECC1549.Main.induced_disjoint_paths
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T09:48:47.157204+00:00
-- url     : https://prove2.me/submissions/1fe4cebc-3093-4513-ba43-747c5bb35f7e

import Theorems.Thm_DirKECC1549_Main_induced_walk_lift
import Theorems.Thm_DirKECC1549_Main_induced_walk_project
set_option autoImplicit false
open DirKECC1549.Main

private theorem disjoint_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (p q : List α)
    (h : Disjoint p.toFinset q.toFinset) : Disjoint (p.map f).toFinset (q.map f).toFinset := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [List.mem_toFinset, List.mem_map] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, eq⟩ := hy
  have : b = a := hf eq
  subst b
  exact Finset.disjoint_left.mp h (List.mem_toFinset.mpr ha) (List.mem_toFinset.mpr hb)

theorem solution {n m : ℕ} (G : Fin m → Fin n × Fin n)
    (S : Finset (Fin n)) (x y : Fin n) (k : ℕ) (hx : x ∈ S) (hy : y ∈ S)
    (hwalk : ∀ p, IsWalk G x p y → ∀ e ∈ p, (G e).1 ∈ S ∧ (G e).2 ∈ S) :
    HasDisjointPaths G k x y ↔
      liftRel S (HasDisjointPaths (induced G S) k) x y := by
  classical
  let f : Fin (inducedEdges G S).card → Fin m :=
    fun i ↦ ((inducedEdges G S).orderIsoOfFin rfl i).1
  have hf : Function.Injective f := by
    intro a b h
    apply (inducedEdges G S).orderIsoOfFin rfl |>.injective
    exact Subtype.ext h
  constructor
  · rintro ⟨P, hp, hd⟩
    have lift : ∀ i, ∃ q, q.map f = P i ∧
        IsWalk (induced G S) (posIn S x hx) q (posIn S y hy) := by
      intro i
      exact induced_walk_lift G S x y hx hy (P i) (hp i).1 (hwalk _ (hp i).1)
    choose Q hQ hW using lift
    refine ⟨hx, hy, Q, ?_, ?_⟩
    · intro i
      exact ⟨hW i, (List.nodup_map_iff hf).mp (by rw [hQ i]; exact (hp i).2)⟩
    · intro i j hij
      apply Finset.disjoint_left.mpr
      intro e he he'
      exact False.elim ((Finset.disjoint_left.mp (hd i j hij) : ∀ ⦃a : Fin m⦄,
        a ∈ (P i).toFinset → a ∈ (P j).toFinset → False) (a := f e)
        (by rw [← hQ i]; simp only [List.mem_toFinset, List.mem_map]; exact ⟨e, List.mem_toFinset.mp he, rfl⟩)
        (by rw [← hQ j]; simp only [List.mem_toFinset, List.mem_map]; exact ⟨e, List.mem_toFinset.mp he', rfl⟩))
  · rintro ⟨_, _, Q, hq, hd⟩
    refine ⟨fun i ↦ (Q i).map f, ?_, ?_⟩
    · intro i
      exact ⟨induced_walk_project G S x y hx hy _ (hq i).1,
        (List.nodup_map_iff hf).mpr (hq i).2⟩
    · intro i j hij
      exact disjoint_map f hf (Q i) (Q j) (hd i j hij)

-- Prove2me | solution 1 for DirKECC1549.Main.edge_menger_avoid
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T10:10:50.090372+00:00
-- url     : https://prove2.me/submissions/26078606-3508-4607-97c2-d922590d27fa

import Theorems.Thm_DirKECC1549_Main_edge_menger_sufficiency
set_option autoImplicit false
open DirKECC1549.Main

theorem solution {n m : ℕ} (D : Fin m → Fin n × Fin n) (k : ℕ)
    (x y : Fin n) : HasDisjointPaths D k x y ↔
    ∀ F : Finset (Fin m), F.card < k → ∃ p, IsWalk D x p y ∧
      ∀ e ∈ p, e ∉ F := by
  classical
  constructor
  · rintro ⟨P, hP, hdis⟩ F hF
    have h : ∃ i, ∀ e ∈ P i, e ∉ F := by
      by_contra hn
      push_neg at hn
      choose edge hedge hmem using hn
      let f : Fin k → {e // e ∈ F} := fun i ↦ ⟨edge i, hmem i⟩
      have hinj : Function.Injective f := by
        intro i j hij
        by_contra hne
        have heq : edge i = edge j := congrArg Subtype.val hij
        have hh := Finset.disjoint_left.mp (hdis i j hne)
          (List.mem_toFinset.mpr (hedge i))
        apply hh
        rw [heq]
        exact List.mem_toFinset.mpr (hedge j)
      have hc := Fintype.card_le_of_injective f hinj
      simp only [Fintype.card_fin, Fintype.card_coe] at hc
      omega
    obtain ⟨i, hi⟩ := h
    exact ⟨P i, (hP i).1, hi⟩
  · exact edge_menger_sufficiency D k x y

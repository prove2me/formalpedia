-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.residual_next_sub
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:22:02.625971+00:00
-- url     : https://prove2.me/submissions/3ff10efe-a841-41ab-8f49-4c253b5c3e27

import Definitions.Def_EdmondsKarp_ShortestPath_Run
import Theorems.Thm_EdmondsKarp_ShortestPath_augment_isFlow

open EdmondsKarp.ShortestPath

private theorem local_augment_residual_sub {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hf : IsFlow N f) (hP : IsAugPath N f P)
    (u v : V) (h : ResArc N (augment N f P) u v) :
    ResArc N f u v ∨ (v, u) ∈ pathArcs P := by
  have he := (augment_isFlow N f P hf hP).1.le
  by_cases hp : (v, u) ∈ pathArcs P
  · exact Or.inr hp
  left
  have hret (x y : V) (hxy : (x, y) ∈ N.A) : ¬ (x = N.t ∧ y = N.s) := by
    rintro ⟨rfl, rfl⟩
    exact N.return_not_mem hxy
  rcases h with ⟨huv, h⟩ | ⟨hvu, h⟩
  · left
    refine ⟨huv, ?_⟩
    have hinc : 0 ≤ augIncrease N f P u v := by
      have hc := sub_nonneg.mpr (hf.2.1 u v huv)
      unfold augIncrease
      split_ifs <;> first | exact le_min he hc | exact he | exact le_rfl
    simp only [augment, hret u v huv, huv, augDecrease, hp, ↓reduceIte] at h
    linarith
  · right
    refine ⟨hvu, ?_⟩
    have hdec : 0 ≤ augDecrease N f P v u := by
      unfold augDecrease
      split_ifs <;> first | exact le_max_left _ _ | exact he | exact le_rfl
    simp only [augment, hret v u hvu, hvu, augIncrease, hp, ↓reduceIte] at h
    linarith

private theorem local_run_isFlow {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P)
    (k : ℕ) (hk : k ≤ K) : IsFlow N (f k) := by
  induction k with
  | zero => exact hrun.1
  | succ k ih =>
    have hkK : k < K := by omega
    obtain ⟨hP, hnext⟩ := hrun.2 k hkK
    rw [hnext]
    exact (augment_isFlow N (f k) (P k) (ih (by omega)) hP.1).2.1

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P)
    (k : ℕ) (hk : k < K) (u v : V) (h : ResArc N (f (k + 1)) u v) :
    ResArc N (f k) u v ∨ (v, u) ∈ pathArcs (P k) := by
  obtain ⟨hP, hnext⟩ := hrun.2 k hk
  rw [hnext] at h
  exact local_augment_residual_sub N (f k) (P k) (local_run_isFlow N K f P hrun k hk.le) hP.1 u v h

-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.bottleneck_not_residual_next
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:22:01.655888+00:00
-- url     : https://prove2.me/submissions/7f1a44b1-fc18-488a-824d-583dedc5c2bf

import Definitions.Def_EdmondsKarp_ShortestPath_Run
import Theorems.Thm_EdmondsKarp_ShortestPath_augment_isFlow

open EdmondsKarp.ShortestPath

private theorem local_pathArcs_simple {V : Type} [Fintype V] [DecidableEq V] (P : List V)
    (hP : P.Nodup) (u v : V) (h : (u, v) ∈ pathArcs P) :
    u ≠ v ∧ (v, u) ∉ pathArcs P ∧ P.head? ≠ some v ∧ P.getLast? ≠ some u := by
  induction P with
  | nil => simp [pathArcs] at h
  | cons a L ih =>
    cases L with
    | nil => simp [pathArcs] at h
    | cons b L =>
      have ha := (List.nodup_cons.mp hP).1
      have ht := (List.nodup_cons.mp hP).2
      have hab : a ≠ b := by intro e; exact ha (by simp [e])
      have hs : pathArcs (a :: b :: L) = (a, b) :: pathArcs (b :: L) := rfl
      rw [hs, List.mem_cons] at h
      rcases h with h | h
      · cases Prod.mk.inj h with
        | intro hu hv =>
          subst u; subst v
          refine ⟨hab, ?_, ?_, ?_⟩
          · rw [hs, List.mem_cons]
            rintro (he | he)
            · exact hab (Prod.mk.inj he).1.symm
            · exact ha (List.mem_of_mem_tail (List.of_mem_zip he).2)
          · simpa using hab
          · rw [List.getLast?_cons_cons]
            intro he
            exact ha (List.mem_of_getLast? he)
      · obtain ⟨hne, hrev, hhead, hlast⟩ := ih ht h
        have hu := (List.of_mem_zip h).1
        have hv := List.mem_of_mem_tail (List.of_mem_zip h).2
        refine ⟨hne, ?_, ?_, ?_⟩
        · rw [hs, List.mem_cons]
          rintro (he | he)
          · exact ha ((Prod.mk.inj he).1 ▸ hv)
          · exact hrev he
        · intro he
          exact ha ((Option.some.inj he).symm ▸ hv)
        · simpa only [List.getLast?_cons_cons] using hlast

private theorem local_augment_bottleneck {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hf : IsFlow N f) (hP : IsAugPath N f P)
    (u v : V) (hb : IsBottleneck N f P u v) :
    ¬ ResArc N (augment N f P) u v := by
  have hp := hb.1
  have hn := (local_pathArcs_simple P hP.1 u v hp).2.1
  have he := hb.2
  have hret (x y : V) (hxy : (x, y) ∈ N.A) : ¬ (x = N.t ∧ y = N.s) := by
    rintro ⟨rfl, rfl⟩
    exact N.return_not_mem hxy
  rintro (⟨huv, h⟩ | ⟨hvu, h⟩)
  · by_cases hvu : (v, u) ∈ N.A
    · have h0 := hf.1 v u (Finset.mem_insert_of_mem hvu)
      simp only [stepEps, huv, hvu, ↓reduceIte] at he
      have hm : min (pathEps N f P) (N.c u v - f u v) = N.c u v - f u v :=
        min_eq_right (by linarith)
      simp only [augment, hret u v huv, huv, augIncrease, augDecrease, hp, hn,
        hvu, ↓reduceIte, hm] at h
      linarith
    · simp only [stepEps, huv, hvu, ↓reduceIte] at he
      simp only [augment, hret u v huv, huv, augIncrease, augDecrease, hp, hn,
        hvu, ↓reduceIte] at h
      linarith
  · by_cases huv : (u, v) ∈ N.A
    · have h0 := hf.1 v u (Finset.mem_insert_of_mem hvu)
      simp only [stepEps, huv, hvu, ↓reduceIte] at he
      have hm : max 0 (pathEps N f P - N.c u v + f u v) = f v u := by
        rw [show pathEps N f P - N.c u v + f u v = f v u by linarith]
        exact max_eq_right h0
      simp only [augment, hret v u hvu, hvu, augIncrease, augDecrease, hp, hn,
        huv, ↓reduceIte, hm] at h
      linarith
    · simp only [stepEps, huv, ↓reduceIte] at he
      simp only [augment, hret v u hvu, hvu, augIncrease, augDecrease, hp, hn,
        huv, ↓reduceIte] at h
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
    (k : ℕ) (hk : k < K) (u v : V)
    (hb : IsBottleneck N (f k) (P k) u v) : ¬ ResArc N (f (k + 1)) u v := by
  obtain ⟨hP, hnext⟩ := hrun.2 k hk
  rw [hnext]
  exact local_augment_bottleneck N (f k) (P k) (local_run_isFlow N K f P hrun k hk.le) hP.1 u v hb

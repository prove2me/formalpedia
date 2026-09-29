-- Prove2me | solution 1 for EdmondsKarp.MaxCapacity.augment_integral
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:53:50.672411+00:00
-- url     : https://prove2.me/submissions/5e5c4119-c81c-413c-8bfc-8f2ad5608ab5

import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation

namespace EdmondsKarp.MaxCapacity

lemma aux_ai_add {a b : ℝ} (ha : ∃ z : ℤ, a = z) (hb : ∃ z : ℤ, b = z) :
    ∃ z : ℤ, a + b = z := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x + y, by push_cast; ring⟩

lemma aux_ai_sub {a b : ℝ} (ha : ∃ z : ℤ, a = z) (hb : ∃ z : ℤ, b = z) :
    ∃ z : ℤ, a - b = z := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x - y, by push_cast; ring⟩

lemma aux_ai_min {a b : ℝ} (ha : ∃ z : ℤ, a = z) (hb : ∃ z : ℤ, b = z) :
    ∃ z : ℤ, min a b = z := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨min x y, by push_cast; rfl⟩

lemma aux_ai_max {a b : ℝ} (ha : ∃ z : ℤ, a = z) (hb : ∃ z : ℤ, b = z) :
    ∃ z : ℤ, max a b = z := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨max x y, by push_cast; rfl⟩

lemma aux_ai_zero : ∃ z : ℤ, (0 : ℝ) = z := ⟨0, by simp⟩

variable {V : Type} [Fintype V] [DecidableEq V]

lemma aux_ai_step (N : Network V) (hcap : IntegralCaps N) (f : V → V → ℝ) (hf : IsFlow N f)
    (hfint : IsIntegralOn N f) (u v : V) (h : ResArc N f u v) :
    ∃ z : ℤ, 0 < z ∧ stepEps N f u v = z := by
  have hA : ∀ p ∈ N.A, p ∈ N.arcs := fun p hp => Finset.mem_insert_of_mem hp
  unfold stepEps
  by_cases h1 : (u, v) ∈ N.A
  · obtain ⟨cz, hcz⟩ := hcap _ h1
    obtain ⟨fz, hfz⟩ := hfint _ (hA _ h1)
    simp only at hcz hfz
    by_cases h2 : (v, u) ∈ N.A
    · obtain ⟨gz, hgz⟩ := hfint _ (hA _ h2)
      simp only at hgz
      refine ⟨cz - fz + gz, ?_, ?_⟩
      · have hle : f u v ≤ N.c u v := hf.2.1 u v h1
        have hge : 0 ≤ f v u := hf.1 v u (hA _ h2)
        have : 0 < N.c u v - f u v + f v u := by
          rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
        rw [hcz, hfz, hgz] at this
        exact_mod_cast this
      · simp [h1, h2, hcz, hfz, hgz]
    · refine ⟨cz - fz, ?_, ?_⟩
      · have : 0 < N.c u v - f u v := by
          rcases h with ⟨_, h⟩ | ⟨h, _⟩
          · exact h
          · exact absurd h h2
        rw [hcz, hfz] at this
        exact_mod_cast this
      · simp [h1, h2, hcz, hfz]
  · rcases h with ⟨h, _⟩ | ⟨h2, hpos⟩
    · exact absurd h h1
    · obtain ⟨gz, hgz⟩ := hfint _ (hA _ h2)
      simp only at hgz
      refine ⟨gz, ?_, ?_⟩
      · rw [hgz] at hpos
        exact_mod_cast hpos
      · simp [h1, hgz]

lemma aux_ai_ne_nil (N : Network V) (f : V → V → ℝ) (P : List V) (hP : IsAugPath N f P) :
    pathArcs P ≠ [] := by
  obtain ⟨_, hh, hl, _⟩ := hP
  match P, hh, hl with
  | [], hh, _ => simp at hh
  | [a], hh, hl =>
    simp at hh hl
    exact absurd (hh.symm.trans hl) N.source_ne_sink
  | a :: b :: rest, _, _ => simp [pathArcs]

lemma aux_ai_eps (N : Network V) (hcap : IntegralCaps N) (f : V → V → ℝ) (P : List V)
    (hf : IsFlow N f) (hfint : IsIntegralOn N f) (hP : IsAugPath N f P) :
    ∃ z : ℤ, 0 < z ∧ pathEps N f P = z := by
  have hne := aux_ai_ne_nil N f P hP
  set L := (pathArcs P).map (fun e => stepEps N f e.1 e.2) with hL
  have hLne : L ≠ [] := by simpa [hL] using hne
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (List.isSome_min?_of_ne_nil hLne)
  have hmem : m ∈ L := List.min?_mem hm
  rw [hL, List.mem_map] at hmem
  obtain ⟨e, he, rfl⟩ := hmem
  have hres : ResArc N f e.1 e.2 := hP.2.2.2 e he
  obtain ⟨z, hz, hze⟩ := aux_ai_step N hcap f hf hfint e.1 e.2 hres
  refine ⟨z, hz, ?_⟩
  unfold pathEps
  rw [← hL, hm]
  simpa using hze

end EdmondsKarp.MaxCapacity

open EdmondsKarp.MaxCapacity

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (hcap : IntegralCaps N) (f : V → V → ℝ) (P : List V) (hf : IsFlow N f)
    (hfint : IsIntegralOn N f) (hP : IsAugPath N f P) :
    (∃ z : ℤ, 0 < z ∧ pathEps N f P = z) ∧ IsIntegralOn N (augment N f P) := by
  have hA : ∀ p ∈ N.A, p ∈ N.arcs := fun p hp => Finset.mem_insert_of_mem hp
  have h1 := aux_ai_eps N hcap f P hf hfint hP
  refine ⟨h1, ?_⟩
  obtain ⟨ez, _, hez⟩ := h1
  have heps : ∃ z : ℤ, pathEps N f P = z := ⟨ez, hez⟩
  rintro ⟨x, y⟩ hp
  have hfxy : ∃ z : ℤ, f x y = z := hfint _ hp
  show ∃ z : ℤ, augment N f P x y = z
  unfold augment
  split_ifs with h1 h2
  · exact aux_ai_add hfxy heps
  · apply aux_ai_sub (aux_ai_add hfxy _) _
    · unfold augIncrease
      split_ifs with h3 h4
      · exact aux_ai_min heps (aux_ai_sub (hcap _ h2) hfxy)
      · exact heps
      · exact aux_ai_zero
    · unfold augDecrease
      split_ifs with h3 h4
      · exact aux_ai_max aux_ai_zero
          (aux_ai_add (aux_ai_sub heps (hcap _ h4)) (hfint _ (hA _ h4)))
      · exact heps
      · exact aux_ai_zero
  · exact hfxy

-- Prove2me | solution 1 for FastReach.mem_reachSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-11T17:35:35.819632+00:00
-- url     : https://prove2.me/submissions/ae91be00-d9e8-4552-a1e5-a0063386c7c2

import Definitions.Def_FastReachability

open Finset SimpleGraph FastReach

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private lemma subset_step' (s : Finset V) : s ⊆ step G s := fun _ hx => by simp [step, hx]

private lemma step_mono' {s t : Finset V} (h : s ⊆ t) : step G s ⊆ step G t := by
  intro x hx
  simp only [step, mem_union, mem_filter, mem_univ, true_and] at hx ⊢
  rcases hx with hx | ⟨u, hu, hadj⟩
  · exact Or.inl (h hx)
  · exact Or.inr ⟨u, h hu, hadj⟩

private lemma iter_mono_set {s t : Finset V} (h : s ⊆ t) (n : ℕ) :
    (step G)^[n] s ⊆ (step G)^[n] t := by
  induction n generalizing s t with
  | zero => simpa using h
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
                 exact ih (step_mono' h)

private lemma subset_iter (s : Finset V) (n : ℕ) : s ⊆ (step G)^[n] s := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.trans (subset_step' _)

private lemma iter_mono_le {s : Finset V} {m n : ℕ} (h : m ≤ n) :
    (step G)^[m] s ⊆ (step G)^[n] s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Function.iterate_add_apply]
  exact iter_mono_set (subset_iter s k) m

private lemma iter_subset_reach (u : V) (n : ℕ) :
    (step G)^[n] {u} ⊆ univ.filter (fun v => G.Reachable u v) := by
  induction n with
  | zero => intro x hx; simp at hx; subst hx; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    intro x hx
    simp only [step, mem_union, mem_filter, mem_univ, true_and] at hx
    rcases hx with hx | ⟨w, hw, hadj⟩
    · exact ih hx
    · have : G.Reachable u w := by simpa using ih hw
      simpa using this.trans hadj.reachable

private lemma mem_iter_of_walk {u v : V} (w : G.Walk u v) : v ∈ (step G)^[w.length] {u} := by
  induction w with
  | nil => simp
  | cons hadj w' ih =>
    rename_i a b _
    have hsub : ({b} : Finset V) ⊆ step G {a} := by
      intro x hx; simp at hx; subst hx
      simp only [step, mem_union, mem_filter, mem_univ, true_and]
      exact Or.inr ⟨a, by simp, hadj⟩
    have h2 := iter_mono_set hsub w'.length ih
    rw [← Function.iterate_succ_apply] at h2
    simpa [Walk.length_cons] using h2

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    v ∈ reachSet G u ↔ G.Reachable u v := by
  constructor
  · intro h; simpa using iter_subset_reach u _ h
  · intro h
    refine h.elim_path fun p => ?_
    exact iter_mono_le (le_of_lt p.2.length_lt) (mem_iter_of_walk p.1)

-- Prove2me | solution 1 for DoubleGreedyUSM.Randomized.endpoint_states
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T12:43:36.541459+00:00
-- url     : https://prove2.me/submissions/38115121-536d-49ba-bce6-b3de2f5d94cb

import Mathlib
import Definitions.Def_DoubleGreedyUSM_Randomized_Algorithm2

set_option autoImplicit false

namespace Pad3a3b57

open DoubleGreedyUSM.Randomized

def Inv {X : Type} (q : List X) (S : Finset X × Finset X) : Prop :=
  ∀ v, (v ∈ q → (v ∈ S.1 ↔ v ∈ S.2)) ∧ (v ∉ q → v ∉ S.1 ∧ v ∈ S.2)

def Good {X : Type} (q : List X) (μ : (Finset X × Finset X) → ℝ) : Prop :=
  ∀ t, 0 ≤ μ t ∧ (μ t ≠ 0 → Inv q t)

lemma addProb_bounds {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (s : Finset X × Finset X) (u : X) : 0 ≤ addProb f s u ∧ addProb f s u ≤ 1 := by
  unfold addProb
  simp only
  have ha : 0 ≤ max (f (insert u s.1) - f s.1) 0 := le_max_right _ _
  have hb : 0 ≤ max (f (s.2.erase u) - f s.2) 0 := le_max_right _ _
  split_ifs with h
  · exact ⟨zero_le_one, le_rfl⟩
  · have hpos : 0 < max (f (insert u s.1) - f s.1) 0 + max (f (s.2.erase u) - f s.2) 0 :=
      lt_of_le_of_ne (by linarith) (Ne.symm h)
    refine ⟨div_nonneg ha hpos.le, ?_⟩
    rw [div_le_one hpos]; linarith

lemma nextMass_nonneg {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (s : Finset X × Finset X) (u : X) (t : Finset X × Finset X) : 0 ≤ nextMass f s u t := by
  have h := addProb_bounds f s u
  unfold nextMass
  have h1 : 0 ≤ (if t = (insert u s.1, s.2) then addProb f s u else 0) := by
    split_ifs <;> linarith
  have h2 : 0 ≤ (if t = (s.1, s.2.erase u) then 1 - addProb f s u else 0) := by
    split_ifs <;> linarith
  linarith

lemma good_step {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (q : List X)
    (μ : (Finset X × Finset X) → ℝ) (u : X) (hu : u ∉ q) (h : Good q μ) :
    Good (q ++ [u]) (advance f μ u) := by
  intro t
  constructor
  · unfold advance
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (h s).1 (nextMass_nonneg f s u t))
  · intro ht
    unfold advance at ht
    obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
    have hμ : μ s ≠ 0 := left_ne_zero_of_mul hs
    have hn : nextMass f s u t ≠ 0 := right_ne_zero_of_mul hs
    have hinv := (h s).2 hμ
    have hu' := (hinv u).2 hu
    have ht' : t = (insert u s.1, s.2) ∨ t = (s.1, s.2.erase u) := by
      by_contra hc
      push Not at hc
      apply hn
      simp [nextMass, hc.1, hc.2]
    intro v
    have hv := hinv v
    rcases ht' with rfl | rfl
    · by_cases hvu : v = u
      · subst hvu
        simp [hu'.2]
      · simpa [List.mem_append, List.mem_singleton, hvu, Finset.mem_insert] using hv
    · by_cases hvu : v = u
      · subst hvu
        simp [hu'.1]
      · simpa [List.mem_append, List.mem_singleton, hvu, Finset.mem_erase] using hv

lemma fold_good {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) :
    ∀ (p q : List X) (μ : (Finset X × Finset X) → ℝ), p.Nodup → (∀ u ∈ p, u ∉ q) → Good q μ →
      Good (q ++ p) (p.foldl (advance f) μ) := by
  intro p
  induction p with
  | nil => intro q μ _ _ h; simpa using h
  | cons u p ih =>
    intro q μ hnd hdis h
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons]
    have h1 := good_step f q μ u (hdis u List.mem_cons_self) h
    have h2 : ∀ w ∈ p, w ∉ q ++ [u] := by
      intro w hw hwq
      rcases List.mem_append.mp hwq with h' | h'
      · exact hdis w (List.mem_cons_of_mem u hw) h'
      · rw [List.mem_singleton] at h'
        exact hnd.1 (h' ▸ hw)
    have := ih (q ++ [u]) (advance f μ u) hnd.2 h2 h1
    simpa using this

lemma state_good {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (l : List X)
    (hl : l.Nodup) (i : ℕ) : Good (l.take i) (state f l i) := by
  have h0 : Good ([] : List X) (fun s => if s = ((∅ : Finset X), (Finset.univ : Finset X)) then 1 else 0) := by
    intro t
    constructor
    · dsimp only
      split_ifs <;> norm_num
    · intro ht v
      dsimp only at ht
      split_ifs at ht with h
      · subst h; simp
      · exact absurd rfl ht
  have := fold_good f (l.take i) [] _ (hl.sublist (List.take_sublist _ _)) (by simp) h0
  simpa [state] using this

end Pad3a3b57

open DoubleGreedyUSM.Randomized in
theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (l : List X) (hl : l.Nodup)
    (hcov : ∀ x : X, x ∈ l) (O : Finset X) :
    (∀ s : Finset X × Finset X,
      state f l 0 s ≠ 0 → s = (∅, Finset.univ) ∧ DoubleGreedyUSM.Deterministic.optI O s = O) ∧
    (∀ s : Finset X × Finset X,
      state f l l.length s ≠ 0 → s.1 = s.2 ∧ DoubleGreedyUSM.Deterministic.optI O s = s.1) := by
  refine ⟨?_, ?_⟩
  · intro s hs
    have hs' : s = ((∅ : Finset X), (Finset.univ : Finset X)) := by
      by_contra hc
      apply hs
      simp [state, hc]
    subst hs'
    refine ⟨rfl, ?_⟩
    ext v; simp [DoubleGreedyUSM.Deterministic.optI]
  · intro s hs
    have hinv := (Pad3a3b57.state_good f l hl l.length s).2 hs
    rw [List.take_length] at hinv
    have heq : s.1 = s.2 := by
      ext v
      exact ((hinv v).1 (hcov v))
    refine ⟨heq, ?_⟩
    ext v
    simp only [DoubleGreedyUSM.Deterministic.optI, Finset.mem_inter, Finset.mem_union]
    rw [← heq]
    tauto

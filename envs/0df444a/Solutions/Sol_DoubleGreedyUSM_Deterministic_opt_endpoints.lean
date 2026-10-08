-- Prove2me | solution 1 for DoubleGreedyUSM.Deterministic.opt_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-05T12:09:29.32699+00:00
-- url     : https://prove2.me/submissions/a6890f57-9eae-4429-b0a1-384087107d68

import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_DoubleGreedyUSM_Deterministic_Algorithm1

open DoubleGreedyUSM.Deterministic

namespace DGProof

variable {X : Type} [Fintype X] [DecidableEq X]

private theorem state_succ (f : Finset X → ℝ) (l : List X) (i : ℕ) (hi : i < l.length) :
    state f l (i + 1) = step f (state f l i) l[i] := by
  unfold state
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
  rfl

private def Inv (p : Finset X) (s : Finset X × Finset X) : Prop :=
  s.1 ⊆ s.2 ∧ ∀ x, (x ∈ s.2 ∧ x ∉ s.1 ↔ x ∉ p)

private theorem inv_step (f : Finset X → ℝ) (p : Finset X) (s : Finset X × Finset X)
    (u : X) (hs : Inv p s) (hu : u ∉ p) : Inv (insert u p) (step f s u) := by
  have huf := (hs.2 u).2 hu
  unfold Inv step
  split
  · constructor
    · intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact huf.1
      · exact hs.1 hx
    · intro x
      by_cases hxu : x = u
      · subst x
        simp
      · simpa [hxu] using hs.2 x
  · constructor
    · intro x hx
      simp only [Finset.mem_erase]
      exact ⟨fun h => huf.2 (h ▸ hx), hs.1 hx⟩
    · intro x
      by_cases hxu : x = u
      · subst x
        simp
      · simpa [hxu] using hs.2 x

private theorem fresh (l : List X) (hl : l.Nodup) (i j : ℕ) (hj : j < l.length)
    (hij : i ≤ j) : l[j] ∉ (l.take i).toFinset := by
  intro hm
  rw [List.mem_toFinset, List.mem_take_iff_getElem] at hm
  obtain ⟨k, hk, he⟩ := hm
  have := hl.getElem_inj_iff.mp he
  omega

private theorem invariant (f : Finset X → ℝ) (l : List X) (hl : l.Nodup)
    (i : ℕ) (hi : i ≤ l.length) : Inv (l.take i).toFinset (state f l i) := by
  induction i with
  | zero => simp [Inv, state]
  | succ i ih =>
    have hil : i < l.length := by omega
    rw [state_succ f l i hil, List.take_succ_eq_append_getElem hil]
    simpa only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
      Finset.union_insert, Finset.union_empty] using
      inv_step f (l.take i).toFinset (state f l i) l[i]
        (ih (by omega)) (fresh l hl i i hil le_rfl)

private theorem unprocessed (f : Finset X → ℝ) (l : List X) (hl : l.Nodup)
    (i j : ℕ) (hj : j < l.length) (hij : i ≤ j) :
    l[j] ∈ (state f l i).2 ∧ l[j] ∉ (state f l i).1 :=
  ((invariant f l hl i (by omega)).2 _).2 (fresh l hl i j hj hij)

private theorem gain_sum (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (s : Finset X × Finset X) (u : X) (hs : s.1 ⊆ s.2)
    (huY : u ∈ s.2) (huX : u ∉ s.1) : 0 ≤ addGain f s u + removeGain f s u := by
  have hunion : insert u s.1 ∪ s.2.erase u = s.2 := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    have hxsub : x ∈ s.1 → x ∈ s.2 := fun hx => hs hx
    by_cases h : x = u <;> aesop
  have hinter : insert u s.1 ∩ s.2.erase u = s.1 := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    have hxsub : x ∈ s.1 → x ∈ s.2 := fun hx => hs hx
    by_cases h : x = u <;> aesop
  have h := hf (insert u s.1) (s.2.erase u)
  rw [hunion, hinter] at h
  dsimp [addGain, removeGain]
  linarith

private theorem processed_agree (f : Finset X → ℝ) (l : List X) (hl : l.Nodup)
    (i : ℕ) (hi : i ≤ l.length) (x : X) (hx : x ∈ (l.take i).toFinset) :
    (x ∈ (state f l i).1 ↔ x ∈ (state f l i).2) := by
  have hs := invariant f l hl i hi
  constructor
  · exact fun hx => hs.1 hx
  · intro hy
    by_contra hn
    exact ((hs.2 x).1 ⟨hy, hn⟩) hx

private theorem final_agree (f : Finset X → ℝ) (l : List X) (hl : l.Nodup)
    (hcov : ∀ x, x ∈ l) : (state f l l.length).1 = (state f l l.length).2 := by
  ext x
  apply processed_agree f l hl l.length le_rfl x
  simpa using hcov x

private theorem opt_add (O : Finset X) (s : Finset X × Finset X) (u : X) (hu : u ∈ s.2) :
    optI O (insert u s.1, s.2) = insert u (optI O s) := by
  ext x
  simp only [optI, Finset.mem_inter, Finset.mem_union, Finset.mem_insert]
  by_cases h : x = u
  · subst x; simp [hu]
  · simp [h]

private theorem opt_remove (O : Finset X) (s : Finset X × Finset X) (u : X) :
    optI O (s.1, s.2.erase u) = (optI O s).erase u := by
  ext x
  simp only [optI, Finset.mem_inter, Finset.mem_union, Finset.mem_erase]
  tauto

private theorem step_loss (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (O : Finset X) (s : Finset X × Finset X) (u : X) (hs : s.1 ⊆ s.2)
    (huY : u ∈ s.2) (huX : u ∉ s.1)
    (hgain : 0 ≤ addGain f s u + removeGain f s u) :
    f (optI O s) - f (optI O (step f s u)) ≤
      (f (step f s u).1 - f s.1) + (f (step f s u).2 - f s.2) := by
  have hxz : s.1 ⊆ optI O s := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inr hx), hs hx⟩
  have hzy : optI O s ⊆ s.2 := Finset.inter_subset_right
  by_cases h : removeGain f s u ≤ addGain f s u
  · simp only [step, if_pos h, Prod.fst, Prod.snd, sub_self, add_zero]
    rw [opt_add O s u huY]
    have ha : 0 ≤ addGain f s u := by linarith
    by_cases hz : u ∈ optI O s
    · rw [Finset.insert_eq_of_mem hz, sub_self]
      exact ha
    · have h' := gain_sum f hf (optI O s, s.2) u hzy huY hz
      dsimp [addGain, removeGain] at h h'
      linarith
  · simp only [step, if_neg h, Prod.fst, Prod.snd, sub_self, zero_add]
    rw [opt_remove]
    have hb : 0 ≤ removeGain f s u := by linarith
    by_cases hz : u ∈ optI O s
    · have h' := gain_sum f hf (s.1, optI O s) u hxz hz huX
      dsimp [addGain, removeGain] at h h'
      linarith
    · rw [Finset.erase_eq_of_notMem hz, sub_self]
      exact hb

end DGProof

open DoubleGreedyUSM.Deterministic

theorem solution {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (O : Finset X) (hO : ∀ S, f S ≤ f O) (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l) :
    (∀ i (hi : i ≤ l.length),
      (∀ j (hj : j < i),
        (l[j]'(by omega) ∈ optI O (state f l i) ↔ l[j]'(by omega) ∈ (state f l i).1) ∧
        (l[j]'(by omega) ∈ optI O (state f l i) ↔ l[j]'(by omega) ∈ (state f l i).2)) ∧
      (∀ j (hj : j < l.length), i ≤ j →
        (l[j] ∈ optI O (state f l i) ↔ l[j] ∈ O))) ∧
    optI O (state f l 0) = O ∧
    optI O (state f l l.length) = (state f l l.length).1 ∧
    (state f l l.length).1 = (state f l l.length).2 := by
  refine ⟨?_, ?_, ?_, DGProof.final_agree f l hl hcov⟩
  · intro i hi
    constructor
    · intro j hj
      have hp : l[j] ∈ (l.take i).toFinset := by
        rw [List.mem_toFinset, List.mem_take_iff_getElem]
        exact ⟨j, by omega, rfl⟩
      have he := DGProof.processed_agree f l hl i hi l[j] hp
      simp only [optI, Finset.mem_inter, Finset.mem_union]
      tauto
    · intro j hj hij
      have hu := DGProof.unprocessed f l hl i j hj hij
      simp [optI, hu.1, hu.2]
  · simp [optI, state]
  · have h := DGProof.final_agree f l hl hcov
    simp [optI, h]



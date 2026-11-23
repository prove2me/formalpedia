-- Prove2me | solution 1 for BeyondGomoryHu.Units.claim_4_7
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:43:31.235266+00:00
-- url     : https://prove2.me/submissions/db1abb47-e1b5-400e-af2e-6ac56305b37e

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

private lemma claim47_isCut_compl {V : Type} [Fintype V] [DecidableEq V]
    {S A : Finset V} (h : IsCut S A) : IsCut S Aᶜ := by
  classical
  rcases h with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  simp only [Finset.mem_inter] at ha
  simp only [Finset.mem_sdiff] at hb
  refine ⟨⟨b, ?_⟩, ⟨a, ?_⟩⟩
  · simp [hb.1, hb.2]
  · simp [ha.1, ha.2]

private lemma claim47_cap_compl {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) (A : Finset V) : cap G Aᶜ = cap G A := by
  classical
  simp only [cap, compl_compl]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact G.symm _ _

private lemma claim47_mincut_compl {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) {S A : Finset V} (h : IsMincut G S A) : IsMincut G S Aᶜ := by
  classical
  refine ⟨claim47_isCut_compl h.1, fun B hB => ?_⟩
  have h' := h.2 Bᶜ (claim47_isCut_compl hB)
  simpa only [claim47_cap_compl] using h'

private lemma claim47_lam_le_cap {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) {S A : Finset V} (h : IsCut S A) :
    lam G S ≤ (cap G A : ℕ∞) := by
  unfold lam
  exact iInf_le_of_le A (iInf_le_of_le h le_rfl)

private lemma claim47_cap_le_lam {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) {S A : Finset V} (h : IsMincut G S A) :
    (cap G A : ℕ∞) ≤ lam G S := by
  unfold lam
  refine le_iInf fun B => le_iInf fun hB => ?_
  exact_mod_cast h.2 B hB

private lemma claim47_lam_eq_cap {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) {S A : Finset V} (h : IsMincut G S A) :
    lam G S = (cap G A : ℕ∞) :=
  le_antisymm (claim47_lam_le_cap G h.1) (claim47_cap_le_lam G h)

private lemma claim47_exists_mincut {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) {S A : Finset V} (hA : IsCut S A) :
    ∃ Z : Finset V, IsMincut G S Z := by
  classical
  let C : Finset (Finset V) := Finset.univ.filter (fun B => IsCut S B)
  have hC : C.Nonempty := ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩⟩
  obtain ⟨Z, hZC, hZ⟩ := Finset.exists_min_image C (fun B => cap G B) hC
  refine ⟨Z, (Finset.mem_filter.mp hZC).2, fun B hB => ?_⟩
  exact hZ B (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩)

private lemma claim47_pair_swap {V : Type} [DecidableEq V] (a b : V) :
    ({a, b} : Finset V) = {b, a} := by
  ext t
  simp [or_comm]

private lemma claim47_oriented_pair_mincut {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) (a b : V) (hab : a ≠ b) :
    ∃ Z : Finset V, IsMincut G {a, b} Z ∧ a ∈ Z ∧ b ∉ Z := by
  classical
  have hc : IsCut {a, b} ({a} : Finset V) := by
    refine ⟨⟨a, by simp⟩, ⟨b, by simp [Ne.symm hab]⟩⟩
  obtain ⟨Z, hZ⟩ := claim47_exists_mincut G hc
  by_cases haZ : a ∈ Z
  · have hbZ : b ∉ Z := by
      intro hbZ
      rcases hZ.1.2 with ⟨t, ht⟩
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at ht
      aesop
    exact ⟨Z, hZ, haZ, hbZ⟩
  · have hbZ : b ∈ Z := by
      rcases hZ.1.1 with ⟨t, ht⟩
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with ⟨htZ, rfl | rfl⟩
      · exact (haZ htZ).elim
      · exact htZ
    refine ⟨Zᶜ, claim47_mincut_compl G hZ, by simp [haZ], by simp [hbZ]⟩

private lemma claim47_cap_as_sum {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) (A : Finset V) :
    cap G A = ∑ a : V, ∑ b : V, if a ∈ A ∧ b ∉ A then G.w a b else 0 := by
  classical
  have hA : Finset.univ.filter (fun a : V => a ∈ A) = A := by
    ext a
    simp
  have hAc : Finset.univ.filter (fun b : V => b ∉ A) = Aᶜ := by
    ext b
    simp
  unfold cap
  calc
    (∑ a ∈ A, ∑ b ∈ Aᶜ, G.w a b) =
        ∑ a ∈ Finset.univ.filter (fun a : V => a ∈ A),
          ∑ b ∈ Finset.univ.filter (fun b : V => b ∉ A), G.w a b := by rw [hA, hAc]
    _ = _ := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases haA : a ∈ A <;> simp [haA]

private lemma claim47_cap_submod {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) (A B : Finset V) :
    cap G (A ∩ B) + cap G (A ∪ B) ≤ cap G A + cap G B := by
  classical
  simp_rw [claim47_cap_as_sum]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro b hb
  by_cases haA : a ∈ A <;> by_cases haB : a ∈ B <;>
    by_cases hbA : b ∈ A <;> by_cases hbB : b ∈ B <;>
      simp [haA, haB, hbA, hbB]

private lemma claim47_lam_single {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) (a : V) : lam G {a} = ⊤ := by
  have hnone : ∀ A : Finset V, ¬ IsCut {a} A := by
    intro A h
    rcases h.1 with ⟨s, hs⟩
    rcases h.2 with ⟨t, ht⟩
    simp only [Finset.mem_inter, Finset.mem_singleton] at hs
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at ht
    rcases hs with ⟨hsA, rfl⟩
    rcases ht with ⟨rfl, htA⟩
    exact htA hsA
  apply le_antisymm le_top
  unfold lam
  exact le_iInf fun A => le_iInf fun hA => (hnone A hA).elim

/-- The preliminary connectivity comparison in the first paragraph of Claim 4.7. -/
private lemma claim47_lam_aw_le {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) (a z w : V) (hlt : lam G {a, z} < lam G {w, z}) :
    lam G {a, w} ≤ lam G {a, z} := by
  classical
  have haz : a ≠ z := by
    intro haz
    subst z
    rw [show ({a, a} : Finset V) = {a} by simp, claim47_lam_single] at hlt
    exact (not_lt_of_ge le_top) hlt
  obtain ⟨Z, hZ, haZ, hzZ⟩ := claim47_oriented_pair_mincut G a z haz
  have hwZ : w ∉ Z := by
    intro hwZ
    have hwzcut : IsCut {w, z} Z := by
      refine ⟨⟨w, by simp [hwZ]⟩, ⟨z, by simp [hzZ]⟩⟩
    have hle : lam G {w, z} ≤ lam G {a, z} := by
      calc
        lam G {w, z} ≤ (cap G Z : ℕ∞) := claim47_lam_le_cap G hwzcut
        _ = lam G {a, z} := (claim47_lam_eq_cap G hZ).symm
    exact (not_le_of_gt hlt) hle
  have hawcut : IsCut {a, w} Z := by
    refine ⟨⟨a, by simp [haZ]⟩, ⟨w, by simp [hwZ]⟩⟩
  calc
    lam G {a, w} ≤ (cap G Z : ℕ∞) := claim47_lam_le_cap G hawcut
    _ = lam G {a, z} := (claim47_lam_eq_cap G hZ).symm

/-- Uncrossing an oriented `{a,b}`-mincut with an oriented `{a,z}`-mincut. -/
private lemma claim47_direct {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) (a b w z : V) (hlt : lam G {a, z} < lam G {w, z})
    (A : Finset V) (hA : IsMincut G {a, b} A)
    (haA : a ∈ A) (hzA : z ∉ A) (hwA : w ∈ A) : False := by
  classical
  have haz : a ≠ z := by
    intro haz
    subst z
    exact hzA haA
  obtain ⟨Y, hY, haY, hzY⟩ := claim47_oriented_pair_mincut G a z haz
  have hI : IsCut {a, b} (A ∩ Y) := by
    refine ⟨⟨a, by simp [haA, haY]⟩, ⟨b, ?_⟩⟩
    have hbA : b ∉ A := by
      intro hbA
      rcases hA.1.2 with ⟨t, ht⟩
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at ht
      aesop
    simp [hbA]
  have hU : IsCut {a, z} (A ∪ Y) := by
    exact ⟨⟨a, by simp [haY]⟩, ⟨z, by simp [hzA, hzY]⟩⟩
  have hUmin : IsMincut G {a, z} (A ∪ Y) := by
    refine ⟨hU, fun B hB => ?_⟩
    have hAI := hA.2 (A ∩ Y) hI
    have hsub := claim47_cap_submod G A Y
    have hYB := hY.2 B hB
    omega
  have hwzcut : IsCut {w, z} (A ∪ Y) := by
    exact ⟨⟨w, by simp [hwA]⟩, ⟨z, by simp [hzA, hzY]⟩⟩
  have hle : lam G {w, z} ≤ lam G {a, z} := by
    calc
      lam G {w, z} ≤ (cap G (A ∪ Y) : ℕ∞) := claim47_lam_le_cap G hwzcut
      _ = lam G {a, z} := (claim47_lam_eq_cap G hUmin).symm
  exact (not_le_of_gt hlt) hle

private lemma claim47_oriented {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) (a b w z : V) (hlt : lam G {a, z} < lam G {w, z})
    (haw : lam G {a, w} ≤ lam G {a, z})
    (A : Finset V) (hA : IsMincut G {a, b} A) (haA : a ∈ A) :
    (w ∈ A ↔ z ∈ A) := by
  classical
  by_cases hwA : w ∈ A <;> by_cases hzA : z ∈ A
  · simp [hwA, hzA]
  · exact (claim47_direct G a b w z hlt A hA haA hzA hwA).elim
  · have hlt' : lam G {a, w} < lam G {z, w} := by
      rw [claim47_pair_swap z w]
      exact lt_of_le_of_lt haw hlt
    exact (claim47_direct G a b z w hlt' A hA haA hwA hzA).elim
  · simp [hwA, hzA]

end BeyondGomoryHu.Units

open BeyondGomoryHu.Units

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (x y w z : V)
    (hlt : min (lam G {x, z}) (lam G {y, z}) < lam G {w, z}) :
    ∀ A : Finset V, IsMincut G {x, y} A → (w ∈ A ↔ z ∈ A) := by
  classical
  clear hG
  intro A hA
  have hxy : (x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A) := by
    rcases hA.1 with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hs
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at ht
    aesop
  rcases min_lt_iff.mp hlt with hxz | hyz
  · have hxw := claim47_lam_aw_le G x z w hxz
    rcases hxy with ⟨hxA, hyA⟩ | ⟨hxA, hyA⟩
    · exact claim47_oriented G x y w z hxz hxw A hA hxA
    · have hc := claim47_oriented G x y w z hxz hxw Aᶜ
        (claim47_mincut_compl G hA) (by simp [hxA])
      have hc' : (w ∉ A ↔ z ∉ A) := by
        simpa only [Finset.mem_compl] using hc
      exact not_iff_not.mp hc'
  · have hyw := claim47_lam_aw_le G y z w hyz
    have hAyx : IsMincut G {y, x} A := by
      rw [claim47_pair_swap y x]
      exact hA
    rcases hxy with ⟨hxA, hyA⟩ | ⟨hxA, hyA⟩
    · have hc := claim47_oriented G y x w z hyz hyw Aᶜ
        (claim47_mincut_compl G hAyx) (by simp [hyA])
      have hc' : (w ∉ A ↔ z ∉ A) := by
        simpa only [Finset.mem_compl] using hc
      exact not_iff_not.mp hc'
    · exact claim47_oriented G y x w z hyz hyw A hAyx hyA

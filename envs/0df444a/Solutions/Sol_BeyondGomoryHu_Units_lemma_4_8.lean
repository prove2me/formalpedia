-- Prove2me | solution 1 for BeyondGomoryHu.Units.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:22:47.059301+00:00
-- url     : https://prove2.me/submissions/e870c550-4e55-4eb0-955b-5bb2b79ebed1

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy
import Theorems.Thm_BeyondGomoryHu_Units_claim_4_7

set_option autoImplicit false

namespace BeyondGomoryHu.Units

private lemma lemma48_isCut_compl {V : Type} [Fintype V] [DecidableEq V]
    {S A : Finset V} (h : IsCut S A) : IsCut S Aᶜ := by
  classical
  rcases h with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  simp only [Finset.mem_inter] at ha
  simp only [Finset.mem_sdiff] at hb
  refine ⟨⟨b, ?_⟩, ⟨a, ?_⟩⟩
  · simp [hb.1, hb.2]
  · simp [ha.1, ha.2]

private lemma lemma48_cap_compl {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) (A : Finset V) : cap G Aᶜ = cap G A := by
  classical
  simp only [cap, compl_compl]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact G.symm _ _

private lemma lemma48_mincut_compl {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) {S A : Finset V} (h : IsMincut G S A) : IsMincut G S Aᶜ := by
  classical
  refine ⟨lemma48_isCut_compl h.1, fun B hB => ?_⟩
  have h' := h.2 Bᶜ (lemma48_isCut_compl hB)
  simpa only [lemma48_cap_compl] using h'

private lemma lemma48_cap_as_sum {V : Type} [Fintype V] [DecidableEq V]
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

private lemma lemma48_cap_submod {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) (A B : Finset V) :
    cap G (A ∩ B) + cap G (A ∪ B) ≤ cap G A + cap G B := by
  classical
  simp_rw [lemma48_cap_as_sum]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro b hb
  by_cases haA : a ∈ A <;> by_cases haB : a ∈ B <;>
    by_cases hbA : b ∈ A <;> by_cases hbB : b ∈ B <;>
      simp [haA, haB, hbA, hbB]

private lemma lemma48_cap_posimod {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) (A B : Finset V) :
    cap G (A \ B) + cap G (B \ A) ≤ cap G A + cap G B := by
  classical
  have h := lemma48_cap_submod G Aᶜ B
  have h₁ : Aᶜ ∩ B = B \ A := by ext x; simp [and_comm]
  have h₂ : (Aᶜ ∪ B)ᶜ = A \ B := by ext x; simp
  rw [h₁, ← lemma48_cap_compl G (Aᶜ ∪ B), h₂, lemma48_cap_compl G A] at h
  omega

private lemma lemma48_mincuts_of_pair {V : Type} [Fintype V] [DecidableEq V]
    {G : WGraph V} {S T A B X Y : Finset V}
    (hA : IsMincut G S A) (hB : IsMincut G T B)
    (hX : IsCut S X) (hY : IsCut T Y)
    (hcap : cap G X + cap G Y ≤ cap G A + cap G B) :
    IsMincut G S X ∧ IsMincut G T Y := by
  constructor
  · refine ⟨hX, fun C hC => ?_⟩
    have hAC := hA.2 C hC
    have hBY := hB.2 Y hY
    omega
  · refine ⟨hY, fun C hC => ?_⟩
    have hAX := hA.2 X hX
    have hBC := hB.2 C hC
    omega

private lemma lemma48_pair_swap {V : Type} [DecidableEq V] (a b : V) :
    ({a, b} : Finset V) = {b, a} := by
  ext t
  simp [or_comm]

/-- The uncrossing step in the reverse direction of Lemma 4.6, with Claim 4.7 replacing
its final appeal to the intersection condition. -/
private lemma lemma48_uncross {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) (hG : G.Connected) (w z x y : V)
    (hlt : min (lam G {x, z}) (lam G {y, z}) < lam G {w, z})
    (M X : Finset V) (hM : IsMincut G {w, z} M) (hwM : w ∈ M) (hzM : z ∉ M)
    (hX : IsMincut G {x, y} X) (hxX : x ∈ X) (hyX : y ∉ X) (hzX : z ∉ X)
    (t v : V) (htX : t ∈ X) (htM : t ∈ M) (hvX : v ∈ X) (hvM : v ∉ M) :
    ∃ Y : Finset V, IsMincut G {x, y} Y ∧ ¬ (v ∈ Y ↔ t ∈ Y) := by
  classical
  have hwX : w ∉ X := by
    intro hwX
    have hwzX := claim_4_7 G hG x y w z hlt X hX
    exact hzX (hwzX.mp hwX)
  by_cases hxM : x ∈ M
  · refine ⟨X ∩ M, ?_, ?_⟩
    · have hI : IsCut {x, y} (X ∩ M) := by
        refine ⟨⟨x, by simp [hxX, hxM]⟩, ⟨y, by simp [hyX]⟩⟩
      have hU : IsCut {w, z} (X ∪ M) := by
        refine ⟨⟨w, by simp [hwM]⟩, ⟨z, by simp [hzX, hzM]⟩⟩
      exact (lemma48_mincuts_of_pair hX hM hI hU (lemma48_cap_submod G X M)).1
    · simp [hvM, htX, htM]
  · refine ⟨X \ M, ?_, ?_⟩
    · have hD : IsCut {x, y} (X \ M) := by
        refine ⟨⟨x, by simp [hxX, hxM]⟩, ⟨y, by simp [hyX]⟩⟩
      have hE : IsCut {w, z} (M \ X) := by
        refine ⟨⟨w, by simp [hwM, hwX]⟩, ⟨z, by simp [hzM]⟩⟩
      exact (lemma48_mincuts_of_pair hX hM hD hE (lemma48_cap_posimod G X M)).1
    · simp [hvX, hvM, htM]

end BeyondGomoryHu.Units

open BeyondGomoryHu.Units

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (μ : Finset V) (hμ : IsNode G μ) (hμ2 : 2 ≤ μ.card)
    {N : Type} [Fintype N] (K : Carcass V N) (hK : IsCarcass G μ K)
    (a : N) (ha : (K.terms a).Nonempty) (T : Set N) (hT : IsAlphaComp K a T) (v : V)
    (hv : Tied K T v) (M : Finset V) (hM : IsMaximizer G K a T v M) (w z : V)
    (hw : w ∈ K.terms a) (hz : z ∈ K.terms a) (hwz : IsOrientedMincut G w z M) (x y : V)
    (hx : x ∈ K.terms a) (hy : y ∈ K.terms a)
    (hzT : ¬ SameUnitSets G x y {z} (compTerms K T))
    (hlt : min (lam G {x, z}) (lam G {y, z}) < lam G {w, z}) :
    ¬ SameUnitSets G x y {v} (compTerms K T) := by
  classical
  obtain ⟨hTM, hvM⟩ : compTerms K T ⊆ (M : Set V) ∧ v ∉ M := by
    rcases hM.1 with ⟨a', ha', b', hb', hMab, hTM, hvM⟩
    exact ⟨hTM, hvM⟩
  simp only [SameUnitSets, Set.mem_singleton_iff, forall_eq] at hzT ⊢
  push_neg at hzT ⊢
  obtain ⟨t, htT, hzt⟩ := hzT
  have htM : t ∈ M := hTM htT
  have separate_of_cut : ∀ X : Finset V, IsMincut G {x, y} X → t ∈ X → z ∉ X →
      ¬ SameUnit G x y v t := by
    intro X hX htX hzX hvt
    by_cases hvX : v ∈ X
    · have hxy : (x ∈ X ∧ y ∉ X) ∨ (x ∉ X ∧ y ∈ X) := by
        rcases hX.1 with ⟨⟨s, hs⟩, ⟨u, hu⟩⟩
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hs
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hu
        aesop
      rcases hxy with ⟨hxX, hyX⟩ | ⟨hxX, hyX⟩
      · obtain ⟨Y, hY, hsep⟩ := lemma48_uncross G hG w z x y hlt M X hwz.1 hwz.2.1
          hwz.2.2 hX hxX hyX hzX t v htX htM hvX hvM
        exact hsep (hvt Y hY)
      · have hlt' : min (lam G {y, z}) (lam G {x, z}) < lam G {w, z} := by
          simpa [min_comm] using hlt
        obtain ⟨Y, hY, hsep⟩ := lemma48_uncross G hG w z y x hlt' M X hwz.1 hwz.2.1
          hwz.2.2 (by simpa only [lemma48_pair_swap x y] using hX) hyX hxX hzX t v htX htM hvX hvM
        have hY' : IsMincut G {x, y} Y := by
          rwa [lemma48_pair_swap x y]
        exact hsep (hvt Y hY')
    · have hmem := hvt X hX
      exact hvX (hmem.mpr htX)
  refine ⟨t, htT, ?_⟩
  unfold SameUnit SEquiv at hzt
  push_neg at hzt
  obtain ⟨X, hX, hsep⟩ := hzt
  rcases hsep with ⟨hzX, htX⟩ | ⟨hzX, htX⟩
  · exact separate_of_cut Xᶜ (lemma48_mincut_compl G hX) (by simp [htX]) (by simp [hzX])
  · exact separate_of_cut X hX htX hzX

-- Prove2me | solution 1 for FairSelling.round_outcome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:11:12.126805+00:00
-- url     : https://prove2.me/submissions/6cb76522-dddf-4c3d-886a-d49b2206e418

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsMatching
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Theorems.Thm_P2M_FairSelling_Canonical_acceptable__8bfd8b611a35
import Theorems.Thm_FairSelling_exists_closed_matching


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ)
    {T : Finset (Fin n)} {R : Finset G} {D : ℝ} {μ : ℝ} {i : Fin n} (hi : i ∈ T)
    {k : ℕ} [NeZero k] (hk : T.card = k)
    (C : Canonical (v i) p μ (τ i) k R D) :
    ∃ (Kset : Finset (Fin n)) (part : Fin n → Fin k),
      i ∈ Kset ∧ Kset ⊆ T ∧ Set.InjOn part Kset ∧
      (∀ a ∈ Kset, τ a ≤ vbarSum (v a) p (C.goods (part a)) + C.cash (part a)) ∧
      (∀ a ∈ T, a ∉ Kset → ∀ b ∈ Kset,
          vbarSum (v a) p (C.goods (part b)) + C.cash (part b) < τ a) ∧
      (∀ a ∈ Kset, a ≠ i → part a ≠ 0) ∧ (Kset = T ∨ part i ≠ 0) := by
  classical
  have hcard : 0 < T.card := Finset.card_pos.mpr ⟨i, hi⟩
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  -- the acceptance relation between the other active agents and the non-special parts
  set acc : Fin n → Fin k → Prop :=
    fun a j => τ a ≤ vbarSum (v a) p (C.goods j) + C.cash j with hacc
  haveI : DecidableRel acc := fun a j => Classical.dec _
  set A : Finset (Fin n) := T.erase i with hA
  set B : Finset (Fin k) := Finset.univ.erase 0 with hB
  have hAB : A.card ≤ B.card := by
    have h1 : A.card = T.card - 1 := by rw [hA, Finset.card_erase_of_mem hi]
    have h2 : B.card = k - 1 := by
      rw [hB, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨K, f, hKA, hinj, hfB, hfacc, hclosed, hlast⟩ :=
    exists_closed_matching acc A.card A B rfl hAB
  -- the part that agent `i` receives
  obtain ⟨j₀, hj₀acc, hj₀not, hj₀last⟩ :
      ∃ j₀ : Fin k, (∀ a ∈ A, a ∉ K → ¬ acc a j₀) ∧ (∀ b ∈ K, j₀ ≠ f b) ∧ (K = A ∨ j₀ ≠ 0) := by
    rcases hlast with hKeq | ⟨b, hbB, hbim, hbacc⟩
    · refine ⟨0, ?_, ?_, Or.inl hKeq⟩
      · intro a ha hna; exact absurd (hKeq ▸ ha) hna
      · intro b hb hcon
        have hmem : f b ∈ B := hfB b hb
        rw [hB] at hmem
        exact (Finset.mem_erase.mp hmem).1 hcon.symm
    · refine ⟨b, hbacc, ?_, Or.inr ?_⟩
      · intro b' hb' hcon
        exact hbim (Finset.mem_image.mpr ⟨b', hb', hcon.symm⟩)
      · rw [hB] at hbB; exact (Finset.mem_erase.mp hbB).1
  refine ⟨insert i K, fun a => if a = i then j₀ else f a, Finset.mem_insert_self _ _, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hi
    · exact Finset.mem_of_mem_erase (hKA ha)
  · intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exfalso
      have hbi : b ≠ a := fun h => (Finset.mem_erase.mp (hKA hb)).1 h
      simp only [if_neg hbi] at hab
      exact hj₀not b hb hab
    · exfalso
      have hai : a ≠ b := fun h => (Finset.mem_erase.mp (hKA ha)).1 h
      simp only [if_neg hai] at hab
      exact hj₀not a ha hab.symm
    · have hai : a ≠ i := fun h => (Finset.mem_erase.mp (hKA ha)).1 h
      have hbi : b ≠ i := fun h => (Finset.mem_erase.mp (hKA hb)).1 h
      simp only [if_neg hai, if_neg hbi] at hab
      exact hinj ha hb hab
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simpa using C.acceptable' j₀
    · have hai : a ≠ i := fun h => (Finset.mem_erase.mp (hKA ha)).1 h
      simp only [if_neg hai]
      exact hfacc a ha
  · intro a haT hna b hb
    have haA : a ∈ A := Finset.mem_erase.mpr ⟨fun h => hna (h ▸ Finset.mem_insert_self _ _), haT⟩
    have haK : a ∉ K := fun h => hna (Finset.mem_insert_of_mem h)
    rcases Finset.mem_insert.mp hb with rfl | hb
    · have := hj₀acc a haA haK
      simpa [hacc, not_le] using this
    · have hbi : b ≠ i := fun h => (Finset.mem_erase.mp (hKA hb)).1 h
      simp only [if_neg hbi]
      have := hclosed a haA haK b hb
      simpa [hacc, not_le] using this
  · intro a ha hai
    simp only [if_neg hai]
    have haK : a ∈ K := by
      rcases Finset.mem_insert.mp ha with rfl | h
      · exact absurd rfl hai
      · exact h
    have hmem : f a ∈ B := hfB a haK
    rw [hB] at hmem
    exact (Finset.mem_erase.mp hmem).1
  · rcases hj₀last with hKeq | hne
    · refine Or.inl ?_
      rw [hKeq, hA, Finset.insert_erase hi]
    · exact Or.inr (by simpa using hne)
end FairSelling

-- Prove2me | solution 1 for CoresConvexGames.Stability.chain_faces_inter_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T18:37:22.052946+00:00
-- url     : https://prove2.me/submissions/2ba14c9c-8eb4-4638-a1b9-5e9b647bcd04

import Mathlib
import Definitions.Def_CoresConvexGames_Stability_CoreFace
import Definitions.Def_CoresConvexGames_Stability_IsRegularConfiguration
import Definitions.Def_CoresConvexGames_Stability_IsCompleteConfiguration

open scoped BigOperators
open Supermodularity.Cooperative

namespace CoresConvexGames.Stability

theorem exists_intermediate_face {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (hreg : IsRegularConfiguration f) (S T : Finset (Fin n)) (hST : S ⊂ T)
    (hcard : S.card + 2 ≤ T.card) (a : Fin n → ℝ) (ha : a ∈ CoreFace f S ∩ CoreFace f T)
    (j k : Fin n) (hj : j ∈ T \ S) (hk : k ∈ T \ S) (hjk : j ≠ k) :
    ∃ (Q : Finset (Fin n)) (b : Fin n → ℝ), S ⊂ Q ∧ Q ⊂ T ∧
      b ∈ CoreFace f S ∩ CoreFace f Q ∩ CoreFace f T ∧
      (∀ i ∈ S, b i = a i) ∧ j ∈ Q ∧ k ∉ Q := by
  classical
  obtain ⟨hjT, hjS⟩ := Finset.mem_sdiff.mp hj
  obtain ⟨hkT, hkS⟩ := Finset.mem_sdiff.mp hk
  let F : Finset (Finset (Fin n)) := Finset.univ.filter (fun Q => j ∈ Q ∧ k ∉ Q)
  have hF : F.Nonempty := by
    refine ⟨{j}, ?_⟩
    simp [F, Ne.symm hjk]
  obtain ⟨P, hP, hmin⟩ := Finset.exists_min_image F (fun Q => (∑ i ∈ Q, a i) - f Q) hF
  have hjP : j ∈ P := ((Finset.mem_filter.mp hP).2).1
  have hkP : k ∉ P := ((Finset.mem_filter.mp hP).2).2
  let d : ℝ := (∑ i ∈ P, a i) - f P
  have hd : 0 ≤ d := sub_nonneg.mpr (ha.1.1.2 P (Finset.subset_univ P))
  have hdm (Q : Finset (Fin n)) (hjQ : j ∈ Q) (hkQ : k ∉ Q) :
      d ≤ (∑ i ∈ Q, a i) - f Q :=
    hmin Q (Finset.mem_filter.mpr ⟨Finset.mem_univ Q, hjQ, hkQ⟩)
  let b : Fin n → ℝ := fun i => a i + (if i = k then d else 0) - (if i = j then d else 0)
  have hsum (Q : Finset (Fin n)) :
      (∑ i ∈ Q, b i) = (∑ i ∈ Q, a i) + (if k ∈ Q then d else 0) - (if j ∈ Q then d else 0) := by
    simp [b, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hb : b ∈ Core Finset.univ f := by
    constructor
    · rw [hsum]
      simpa using ha.1.1.1
    · intro Q _
      have hqa := ha.1.1.2 Q (Finset.subset_univ Q)
      rw [hsum]
      by_cases hjQ : j ∈ Q <;> by_cases hkQ : k ∈ Q <;> simp only [hjQ, hkQ, ↓reduceIte]
      · linarith
      · have := hdm Q hjQ hkQ
        linarith
      · linarith
      · linarith
  have hbS : b ∈ CoreFace f S := by
    refine ⟨hb, fun hS => ?_⟩
    rw [hsum]
    simpa [hjS, hkS] using ha.1.2 hS
  have hbT : b ∈ CoreFace f T := by
    refine ⟨hb, fun hT => ?_⟩
    rw [hsum]
    simpa [hjT, hkT] using ha.2.2 hT
  have hbP : b ∈ CoreFace f P := by
    refine ⟨hb, fun _ => ?_⟩
    rw [hsum]
    simp [hjP, hkP, d]
  let Q := (S ∪ P) ∩ T
  have hbQ : b ∈ CoreFace f Q :=
    (hreg.2 (S ∪ P) T ⟨(hreg.2 S P ⟨hbS, hbP⟩).1, hbT⟩).2
  have hSQ : S ⊆ Q := by
    intro i hi
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_left P hi, hST.subset hi⟩
  have hjQ : j ∈ Q :=
    Finset.mem_inter.mpr ⟨Finset.mem_union_right S hjP, hjT⟩
  have hkQ : k ∉ Q := by
    intro h
    rcases Finset.mem_union.mp (Finset.mem_inter.mp h).1 with h | h
    · exact hkS h
    · exact hkP h
  refine ⟨Q, b, Finset.ssubset_iff_subset_ne.mpr ⟨hSQ, ?_⟩,
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, ?_⟩,
    ⟨⟨hbS, hbQ⟩, hbT⟩, ?_, hjQ, hkQ⟩
  · intro h
    exact hjS (h ▸ hjQ)
  · intro h
    exact hkQ (h.symm ▸ hkT)
  · intro i hi
    have hij : i ≠ j := ne_of_mem_of_not_mem hi hjS
    have hik : i ≠ k := ne_of_mem_of_not_mem hi hkS
    simp [b, hij, hik]

end CoresConvexGames.Stability


open scoped BigOperators
open Supermodularity.Cooperative

namespace CoresConvexGames.Stability

theorem face_sum_eq {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    {S : Finset (Fin n)} {a : Fin n → ℝ} (ha : a ∈ CoreFace f S) :
    (∑ i ∈ S, a i) = f S := by
  by_cases hS : S.Nonempty
  · exact ha.2 hS
  · have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [this, hf0]

theorem tight_insert_between {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (hreg : IsRegularConfiguration f) (T S : Finset (Fin n)) (hST : S ⊆ T)
    (a : Fin n → ℝ) (ha : a ∈ CoreFace f S ∩ CoreFace f T)
    (j : Fin n) (hj : j ∈ T \ S) :
    ∃ b ∈ CoreFace f (insert j S), ∀ i ∈ S, b i = a i := by
  classical
  induction T using Finset.strongInductionOn generalizing S a j with
  | _ T ih =>
    obtain ⟨hjT, hjS⟩ := Finset.mem_sdiff.mp hj
    by_cases he : insert j S = T
    · exact ⟨a, he.symm ▸ ha.2, fun _ _ => rfl⟩
    have his : insert j S ⊆ T := Finset.insert_subset_iff.mpr ⟨hjT, hST⟩
    have hlt : insert j S ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨his, he⟩
    obtain ⟨k, hkT, hkI⟩ := Finset.exists_of_ssubset hlt
    have hkS : k ∉ S := fun h => hkI (Finset.mem_insert_of_mem h)
    have hjk : j ≠ k := by
      intro h
      exact hkI (h ▸ Finset.mem_insert_self j S)
    have hcard : S.card + 2 ≤ T.card := by
      have hc := Finset.card_lt_card hlt
      rw [Finset.card_insert_of_notMem hjS] at hc
      omega
    have hstrict : S ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hST, by
      intro h
      exact hjS (h.symm ▸ hjT)⟩
    obtain ⟨Q, b, hSQ, hQT, hb, hba, hjQ, _⟩ :=
      exists_intermediate_face f hf0 hreg S T hstrict hcard a ha j k
        (Finset.mem_sdiff.mpr ⟨hjT, hjS⟩) (Finset.mem_sdiff.mpr ⟨hkT, hkS⟩) hjk
    obtain ⟨c, hc, hcb⟩ := ih Q hQT S hSQ.subset b hb.1 j
      (Finset.mem_sdiff.mpr ⟨hjQ, hjS⟩)
    exact ⟨c, hc, fun i hi => (hcb i hi).trans (hba i hi)⟩

theorem tight_face_extension {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (hreg : IsRegularConfiguration f) (S T : Finset (Fin n)) (hST : S ⊆ T)
    (a : Fin n → ℝ) (ha : a ∈ CoreFace f S) :
    ∃ b ∈ CoreFace f T, ∀ i ∈ S, b i = a i := by
  classical
  have aux (R : Finset (Fin n)) :
      ∃ c ∈ CoreFace f (S ∪ R), ∀ i ∈ S, c i = a i := by
    induction R using Finset.induction_on with
    | empty => simpa using ⟨a, ha, fun _ _ => rfl⟩
    | @insert j R hj ih =>
      obtain ⟨c, hc, heq⟩ := ih
      by_cases hjS : j ∈ S ∪ R
      · have hu : S ∪ insert j R = S ∪ R := by
          rw [Finset.union_insert, Finset.insert_eq_of_mem hjS]
        exact ⟨c, hu.symm ▸ hc, heq⟩
      · have hcN : c ∈ CoreFace f Finset.univ := ⟨hc.1, fun _ => hc.1.1⟩
        obtain ⟨d, hd, hdc⟩ := tight_insert_between f hf0 hreg Finset.univ (S ∪ R)
          (Finset.subset_univ _) c ⟨hc, hcN⟩ j
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjS⟩)
        rw [Finset.union_insert]
        exact ⟨d, hd, fun i hi => (hdc i (Finset.mem_union_left R hi)).trans (heq i hi)⟩
  obtain ⟨b, hb, heq⟩ := aux T
  have hu : S ∪ T = T := Finset.union_eq_right.mpr hST
  exact ⟨b, hu ▸ hb, heq⟩

theorem exists_tight_pair {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (hreg : IsRegularConfiguration f) (S T : Finset (Fin n)) (hST : S ⊆ T) :
    (CoreFace f S ∩ CoreFace f T).Nonempty := by
  obtain ⟨a, ha⟩ := hreg.1
  have ha0 : a ∈ CoreFace f ∅ := ⟨ha.1, fun h => by simpa using h⟩
  obtain ⟨b, hb, _⟩ := tight_face_extension f hf0 hreg ∅ S (Finset.empty_subset _) a ha0
  obtain ⟨c, hc, heq⟩ := tight_face_extension f hf0 hreg S T hST b hb
  refine ⟨c, ⟨hc.1, ?_⟩, hc⟩
  intro hS
  calc (∑ i ∈ S, c i) = ∑ i ∈ S, b i := Finset.sum_congr rfl heq
    _ = f S := hb.2 hS


end CoresConvexGames.Stability


open scoped BigOperators
open Supermodularity.Cooperative

namespace CoresConvexGames.Stability

theorem chain_faces_inter_nonempty {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (hreg : IsRegularConfiguration f) :
    (∀ (m : ℕ) (S : Fin (m + 1) → Finset (Fin n)), StrictMono S →
      (⋂ k, CoreFace f (S k)).Nonempty) ∧
    IsCompleteConfiguration f := by
  classical
  have hface (S : Finset (Fin n)) : (CoreFace f S).Nonempty := by
    obtain ⟨a, ha, _⟩ := exists_tight_pair f hf0 hreg S S (Finset.Subset.refl S)
    exact ⟨a, ha⟩
  have hchain : ∀ (m : ℕ) (S : Fin (m + 1) → Finset (Fin n)), StrictMono S →
      ∃ a, ∀ k, a ∈ CoreFace f (S k) := by
    intro m
    induction m with
    | zero =>
      intro S _
      obtain ⟨a, ha⟩ := hface (S 0)
      exact ⟨a, fun i => by
        have hi : i = 0 := by apply Fin.ext; omega
        simpa [hi] using ha⟩
    | succ m ih =>
      intro S hS
      let S' : Fin (m + 1) → Finset (Fin n) := fun i => S i.castSucc
      have hS' : StrictMono S' := by
        intro i j hij
        exact hS hij
      obtain ⟨a, ha⟩ := ih S' hS'
      have hlast : S' (Fin.last m) ⊆ S (Fin.last (m + 1)) :=
        (hS (Fin.castSucc_lt_last _)).le
      obtain ⟨b, hb, hba⟩ := tight_face_extension f hf0 hreg
        (S' (Fin.last m)) (S (Fin.last (m + 1))) hlast a (ha (Fin.last m))
      refine ⟨b, ?_⟩
      intro k
      refine Fin.lastCases hb (fun i => ?_) k
      refine ⟨hb.1, fun hi => ?_⟩
      have hsub : S' i ⊆ S' (Fin.last m) := hS'.monotone (Fin.le_last i)
      calc (∑ j ∈ S i.castSucc, b j) = ∑ j ∈ S' i, a j := by
              apply Finset.sum_congr rfl
              exact fun j hj => hba j (hsub hj)
        _ = f (S i.castSucc) := (ha i).2 hi
  refine ⟨?_, hface⟩
  intro m S hS
  obtain ⟨a, ha⟩ := hchain m S hS
  exact ⟨a, Set.mem_iInter.mpr ha⟩

end CoresConvexGames.Stability


theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (hreg : CoresConvexGames.Stability.IsRegularConfiguration f) :
    (∀ (m : ℕ) (S : Fin (m + 1) → Finset (Fin n)), StrictMono S →
      (⋂ k, CoresConvexGames.Stability.CoreFace f (S k)).Nonempty) ∧
    CoresConvexGames.Stability.IsCompleteConfiguration f :=
  CoresConvexGames.Stability.chain_faces_inter_nonempty f hf0 hreg

#print axioms solution

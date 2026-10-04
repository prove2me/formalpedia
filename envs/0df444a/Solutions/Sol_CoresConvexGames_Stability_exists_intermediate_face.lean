-- Prove2me | solution 1 for CoresConvexGames.Stability.exists_intermediate_face
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T18:24:59.132797+00:00
-- url     : https://prove2.me/submissions/655a4538-a5ca-49b8-a325-98b6ae322ec2

import Mathlib
import Definitions.Def_CoresConvexGames_Stability_CoreFace
import Definitions.Def_CoresConvexGames_Stability_IsRegularConfiguration

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


theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (hreg : CoresConvexGames.Stability.IsRegularConfiguration f)
    (S T : Finset (Fin n)) (hST : S ⊂ T) (hcard : S.card + 2 ≤ T.card)
    (a : Fin n → ℝ)
    (ha : a ∈ CoresConvexGames.Stability.CoreFace f S ∩ CoresConvexGames.Stability.CoreFace f T)
    (j k : Fin n) (hj : j ∈ T \ S) (hk : k ∈ T \ S) (hjk : j ≠ k) :
    ∃ (Q : Finset (Fin n)) (b : Fin n → ℝ), S ⊂ Q ∧ Q ⊂ T ∧
      b ∈ CoresConvexGames.Stability.CoreFace f S ∩ CoresConvexGames.Stability.CoreFace f Q ∩
        CoresConvexGames.Stability.CoreFace f T ∧
      (∀ i ∈ S, b i = a i) ∧ j ∈ Q ∧ k ∉ Q :=
  CoresConvexGames.Stability.exists_intermediate_face f hf0 hreg S T hST hcard a ha j k hj hk hjk

#print axioms solution

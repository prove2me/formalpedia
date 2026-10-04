-- Prove2me | solution 1 for CoresConvexGames.Stability.convex_iff_regular
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T18:31:21.768265+00:00
-- url     : https://prove2.me/submissions/eecf88d9-6588-401e-856d-10e0954ebc8d

import Mathlib
import Definitions.Def_CoresConvexGames_Stability_CoreFace
import Definitions.Def_CoresConvexGames_Stability_IsRegularConfiguration
import Definitions.Def_Supermodularity_Cooperative_IsConvexGame

open scoped BigOperators

namespace CoresConvexGames.Proof

open Supermodularity.Cooperative

theorem extend_one {n : ℕ} (f : Finset (Fin n) → ℝ) (hf : IsConvexGame f)
    (S : Finset (Fin n)) (a : Fin n → ℝ) (ha : a ∈ Core S f)
    (j : Fin n) (hj : j ∉ S) :
    ∃ c ∈ Core (insert j S) f, ∀ i ∈ S, c i = a i := by
  classical
  let c := Function.update a j (f (insert j S) - f S)
  have hc : ∀ i ∈ S, c i = a i := by
    intro i hi
    exact Function.update_of_ne (ne_of_mem_of_not_mem hi hj) _ _
  have hsum : ∑ i ∈ S, c i = f S := by
    rw [Finset.sum_congr rfl hc]
    exact ha.1
  refine ⟨c, ⟨?_, ?_⟩, hc⟩
  · rw [Finset.sum_insert hj, hsum]
    simp [c]
  · intro T hT
    by_cases hjT : j ∈ T
    · have hTS : T.erase j ⊆ S := by
        intro i hi
        have hit := hT (Finset.mem_of_mem_erase hi)
        rcases Finset.mem_insert.mp hit with rfl | his
        · exact False.elim ((Finset.ne_of_mem_erase hi) rfl)
        · exact his
      have hTU : T ∪ S = insert j S := by
        ext i
        constructor
        · intro hi
          rcases Finset.mem_union.mp hi with hit | his
          · exact hT hit
          · exact Finset.mem_insert_of_mem his
        · intro hi
          rcases Finset.mem_insert.mp hi with rfl | his
          · exact Finset.mem_union_left S hjT
          · exact Finset.mem_union_right T his
      have hTI : T ∩ S = T.erase j := by
        ext i
        simp only [Finset.mem_inter, Finset.mem_erase]
        constructor
        · rintro ⟨hiT, hiS⟩
          exact ⟨ne_of_mem_of_not_mem hiS hj, hiT⟩
        · rintro ⟨hij, hiT⟩
          exact ⟨hiT, hTS (Finset.mem_erase.mpr ⟨hij, hiT⟩)⟩
      have hsm := hf.2 (x := T) (Set.mem_univ T) (y := S) (Set.mem_univ S)
      change f T + f S ≤ f (T ∪ S) + f (T ∩ S) at hsm
      rw [hTU, hTI] at hsm
      have hacc := ha.2 (T.erase j) hTS
      have hcsum : ∑ i ∈ T.erase j, c i = ∑ i ∈ T.erase j, a i :=
        Finset.sum_congr rfl (fun i hi => hc i (hTS hi))
      rw [← Finset.sum_erase_add _ _ hjT, hcsum]
      have hcj : c j = f (insert j S) - f S := by simp [c]
      rw [hcj]
      linarith
    · have hTS : T ⊆ S := by
        intro i hi
        rcases Finset.mem_insert.mp (hT hi) with rfl | his
        · exact False.elim (hjT hi)
        · exact his
      calc f T ≤ ∑ i ∈ T, a i := ha.2 T hTS
        _ = ∑ i ∈ T, c i := (Finset.sum_congr rfl (fun i hi => hc i (hTS hi))).symm

theorem core_extension {n : ℕ} (f : Finset (Fin n) → ℝ) (hf : IsConvexGame f)
    (S : Finset (Fin n)) (a : Fin n → ℝ) (ha : a ∈ Core S f) :
    ∃ c ∈ Core Finset.univ f, ∀ i ∈ S, c i = a i := by
  classical
  have aux (R : Finset (Fin n)) :
      ∃ c ∈ Core (S ∪ R) f, ∀ i ∈ S, c i = a i := by
    induction R using Finset.induction_on with
    | empty => simpa using ⟨a, ha, fun i (_ : i ∈ S) => rfl⟩
    | @insert j R hj ih =>
      obtain ⟨c, hc, heq⟩ := ih
      by_cases hjS : j ∈ S ∪ R
      · have hu : S ∪ insert j R = S ∪ R := by
          rw [Finset.union_insert, Finset.insert_eq_of_mem hjS]
        rw [hu]
        exact ⟨c, hc, heq⟩
      · obtain ⟨d, hd, hdc⟩ := extend_one f hf (S ∪ R) c hc j hjS
        rw [Finset.union_insert]
        refine ⟨d, hd, ?_⟩
        intro i hi
        exact (hdc i (Finset.mem_union_left R hi)).trans (heq i hi)
  obtain ⟨c, hc, heq⟩ := aux Finset.univ
  have hu : S ∪ Finset.univ = Finset.univ := by
    ext i
    simp
  exact ⟨c, hu ▸ hc, heq⟩

theorem core_nonempty {n : ℕ} (f : Finset (Fin n) → ℝ) (hf : IsConvexGame f) :
    (Core Finset.univ f).Nonempty := by
  have hz : (0 : Fin n → ℝ) ∈ Core ∅ f := by
    constructor
    · simpa using hf.1.symm
    · intro S hS
      have : S = ∅ := Finset.subset_empty.mp hS
      simp [this, hf.1]
  obtain ⟨c, hc, _⟩ := core_extension f hf ∅ 0 hz
  exact ⟨c, hc⟩

end CoresConvexGames.Proof


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

theorem convex_iff_regular {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0) :
    IsConvexGame f ↔ IsRegularConfiguration f := by
  classical
  constructor
  · intro hf
    obtain ⟨a, ha⟩ := CoresConvexGames.Proof.core_nonempty f hf
    refine ⟨⟨a, ha, fun _ => ha.1⟩, ?_⟩
    intro S T x hx
    have hS := face_sum_eq f hf0 hx.1
    have hT := face_sum_eq f hf0 hx.2
    have hU := hx.1.1.2 (S ∪ T) (Finset.subset_univ _)
    have hI := hx.1.1.2 (S ∩ T) (Finset.subset_univ _)
    have hsm := hf.2 (x := S) (Set.mem_univ _) (y := T) (Set.mem_univ _)
    change f S + f T ≤ f (S ∪ T) + f (S ∩ T) at hsm
    have hsum : (∑ i ∈ S ∪ T, x i) + (∑ i ∈ S ∩ T, x i) =
        (∑ i ∈ S, x i) + (∑ i ∈ T, x i) := Finset.sum_union_inter
    refine ⟨⟨hx.1.1, fun _ => ?_⟩, ⟨hx.1.1, fun _ => ?_⟩⟩ <;> linarith
  · intro hreg
    refine ⟨hf0, ?_⟩
    intro S _ T _
    obtain ⟨a, haS, haT⟩ := exists_tight_pair f hf0 hreg (S ∩ T) (S ∪ T)
      (fun i hi => Finset.mem_union_left T (Finset.mem_inter.mp hi).1)
    have hI := face_sum_eq f hf0 haS
    have hU := face_sum_eq f hf0 haT
    have hS := haS.1.2 S (Finset.subset_univ _)
    have hT := haS.1.2 T (Finset.subset_univ _)
    have hsum : (∑ i ∈ S ∪ T, a i) + (∑ i ∈ S ∩ T, a i) =
        (∑ i ∈ S, a i) + (∑ i ∈ T, a i) := Finset.sum_union_inter
    change f S + f T ≤ f (S ∪ T) + f (S ∩ T)
    linarith

end CoresConvexGames.Stability


theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0) :
    Supermodularity.Cooperative.IsConvexGame f ↔ CoresConvexGames.Stability.IsRegularConfiguration f :=
  CoresConvexGames.Stability.convex_iff_regular f hf0

#print axioms solution

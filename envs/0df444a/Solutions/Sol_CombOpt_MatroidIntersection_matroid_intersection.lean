-- Prove2me | solution 1 for CombOpt.MatroidIntersection.matroid_intersection
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T05:49:12.176383+00:00
-- url     : https://prove2.me/submissions/193d191b-5065-40a0-bef8-0b3e634eb724

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersection_Matroid
import Definitions.Def_CombOpt_MatroidIntersection_rank

set_option autoImplicit false

namespace MIAux
open CombOpt.MatroidIntersection EdmondsPartition.Main

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma indep_empty (M : CombOpt.MatroidIntersection.Matroid S) : M.Indep ∅ := M.isMatroid.1

lemma indep_sub (M : CombOpt.MatroidIntersection.Matroid S) {J' J : Finset S} (h : J' ⊆ J)
    (hJ : M.Indep J) : M.Indep J' :=
  M.isMatroid.2.1 J' J h hJ

lemma exists_basis_ext (M : CombOpt.MatroidIntersection.Matroid S) {A J : Finset S}
    (hJA : J ⊆ A) (hJ : M.Indep J) : ∃ B, J ⊆ B ∧ IsMaxIndepIn M.Indep A B := by
  classical
  have hne : (A.powerset.filter (fun B => M.Indep B ∧ J ⊆ B)).Nonempty :=
    ⟨J, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hJA, hJ, le_refl _⟩⟩
  obtain ⟨B, hB, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  rw [Finset.mem_filter, Finset.mem_powerset] at hB
  refine ⟨B, hB.2.2, hB.1, hB.2.1, fun B' hBB' hB'A hB' => ?_⟩
  have := hmax B' (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hB'A, hB', hB.2.2.trans hBB'⟩)
  exact (Finset.eq_of_subset_of_card_le hBB' this).symm

lemma basis_card (M : CombOpt.MatroidIntersection.Matroid S) {A B : Finset S}
    (hB : IsMaxIndepIn M.Indep A B) : B.card = rank M.Indep A := by
  classical
  apply le_antisymm
  · unfold rank
    exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hB.1, hB⟩)
  · unfold rank
    apply Finset.sup_le
    intro B' hB'
    rw [Finset.mem_filter] at hB'
    exact le_of_eq (M.isMatroid.2.2 A B' B hB'.2 hB)

lemma exists_basis (M : CombOpt.MatroidIntersection.Matroid S) (A : Finset S) :
    ∃ B, IsMaxIndepIn M.Indep A B := by
  obtain ⟨B, -, hB⟩ := exists_basis_ext M (Finset.empty_subset A) (indep_empty M)
  exact ⟨B, hB⟩

lemma card_le_rank (M : CombOpt.MatroidIntersection.Matroid S) {A J : Finset S} (hJA : J ⊆ A)
    (hJ : M.Indep J) : J.card ≤ rank M.Indep A := by
  obtain ⟨B, hJB, hB⟩ := exists_basis_ext M hJA hJ
  rw [← basis_card M hB]; exact Finset.card_le_card hJB

lemma rank_le_card (M : CombOpt.MatroidIntersection.Matroid S) (A : Finset S) :
    rank M.Indep A ≤ A.card := by
  obtain ⟨B, hB⟩ := exists_basis M A
  rw [← basis_card M hB]; exact Finset.card_le_card hB.1

lemma rank_of_indep (M : CombOpt.MatroidIntersection.Matroid S) {X : Finset S}
    (h : M.Indep X) : rank M.Indep X = X.card :=
  le_antisymm (rank_le_card M X) (card_le_rank M (le_refl _) h)

lemma indep_of_card_le_rank (M : CombOpt.MatroidIntersection.Matroid S) {X : Finset S}
    (h : X.card ≤ rank M.Indep X) : M.Indep X := by
  obtain ⟨B, hB⟩ := exists_basis M X
  rw [← basis_card M hB] at h
  have := Finset.eq_of_subset_of_card_le hB.1 h
  rw [← this]; exact hB.2.1

lemma rank_submod (M : CombOpt.MatroidIntersection.Matroid S) (X Y : Finset S) :
    rank M.Indep (X ∩ Y) + rank M.Indep (X ∪ Y) ≤ rank M.Indep X + rank M.Indep Y := by
  obtain ⟨B, hB⟩ := exists_basis M (X ∩ Y)
  have hsub : B ⊆ X ∪ Y := fun x hx => by
    have := hB.1 hx
    rw [Finset.mem_inter] at this
    exact Finset.mem_union_left _ this.1
  obtain ⟨B', hBB', hB'⟩ := exists_basis_ext M hsub hB.2.1
  rw [← basis_card M hB, ← basis_card M hB']
  have h1 : (B' ∩ X).card ≤ rank M.Indep X :=
    card_le_rank M Finset.inter_subset_right (indep_sub M Finset.inter_subset_left hB'.2.1)
  have h2 : (B' ∩ Y).card ≤ rank M.Indep Y :=
    card_le_rank M Finset.inter_subset_right (indep_sub M Finset.inter_subset_left hB'.2.1)
  have h4 := Finset.card_union_add_card_inter (B' ∩ X) (B' ∩ Y)
  have h5 : (B' ∩ X) ∪ (B' ∩ Y) = B' := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      have := hB'.1 hx
      rw [Finset.mem_union] at this
      rcases this with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have h6 : B.card ≤ ((B' ∩ X) ∩ (B' ∩ Y)).card := by
    apply Finset.card_le_card
    intro x hx
    have a := hBB' hx
    have b := hB.1 hx
    simp only [Finset.mem_inter] at b ⊢
    exact ⟨⟨a, b.1⟩, a, b.2⟩
  rw [h5] at h4
  omega

lemma indep_insert_of_lt (M : CombOpt.MatroidIntersection.Matroid S) {C X : Finset S} {e : S}
    (hCX : C ⊆ X) (heX : e ∉ X) (hC : M.Indep C)
    (h : rank M.Indep X < rank M.Indep (insert e X)) : M.Indep (insert e C) := by
  have hs := rank_submod M X (insert e C)
  have hi : X ∩ insert e C = C := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hx' | hx'⟩
      · subst hx'; exact absurd hx heX
      · exact hx'
    · intro hx; exact ⟨hCX hx, Or.inr hx⟩
  have hu : X ∪ insert e C = insert e X := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro (hx | hx | hx)
      · exact Or.inr hx
      · exact Or.inl hx
      · exact Or.inr (hCX hx)
    · rintro (hx | hx)
      · exact Or.inr (Or.inl hx)
      · exact Or.inl hx
  rw [hi, hu, rank_of_indep M hC] at hs
  have heC : e ∉ C := fun h' => heX (hCX h')
  apply indep_of_card_le_rank
  rw [Finset.card_insert_of_notMem heC]
  omega

lemma setid1 {e : S} {A1 A2 C : Finset S} (h1 : e ∉ A1) (hC : e ∉ C) :
    (A1 ∪ C) ∩ (A2 ∪ insert e C) = (A1 ∩ A2) ∪ C := by
  ext x
  by_cases hx : x = e
  · subst hx; simp [h1, hC]
  · simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_insert, hx, false_or]
    tauto

lemma setid2 {e : S} {A1 A2 C : Finset S} :
    (A1 ∪ C) ∪ (A2 ∪ insert e C) = insert e (A1 ∪ A2) ∪ C := by
  ext x
  by_cases hx : x = e
  · subst hx; simp
  · simp only [Finset.mem_union, Finset.mem_insert, hx, false_or]
    tauto

lemma setid3 {e : S} {T' A1 A2 C : Finset S} (hT : e ∉ T') (hC : e ∉ C) :
    ((T' \ A1) ∪ C) ∩ ((T' \ A2) ∪ insert e C)
      = (insert e T' \ insert e (A1 ∪ A2)) ∪ C := by
  ext x
  by_cases hx : x = e
  · subst hx; simp [hT, hC]
  · simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, hx,
      false_or]
    tauto

lemma setid4 {e : S} {T' A1 A2 C : Finset S} (h1 : e ∉ A1) :
    ((T' \ A1) ∪ C) ∪ ((T' \ A2) ∪ insert e C) = (insert e T' \ (A1 ∩ A2)) ∪ C := by
  ext x
  by_cases hx : x = e
  · subst hx; simp [h1]
  · simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, hx,
      false_or]
    tauto

theorem main (M₁ M₂ : CombOpt.MatroidIntersection.Matroid S) (T : Finset S) :
    ∀ C : Finset S, Disjoint C T → M₁.Indep C → M₂.Indep C →
    ∃ J, J ⊆ T ∧ M₁.Indep (J ∪ C) ∧ M₂.Indep (J ∪ C) ∧ ∃ A, A ⊆ T ∧
      rank M₁.Indep (A ∪ C) + rank M₂.Indep ((T \ A) ∪ C) ≤ J.card + 2 * C.card := by
  induction T using Finset.induction_on with
  | empty =>
    intro C _ h1 h2
    refine ⟨∅, le_refl _, by simpa using h1, by simpa using h2, ∅, le_refl _, ?_⟩
    simp only [Finset.empty_union, Finset.sdiff_empty, Finset.card_empty]
    rw [rank_of_indep M₁ h1, rank_of_indep M₂ h2]
    omega
  | insert e T' heT ih =>
    intro C hdisj h1 h2
    have heC : e ∉ C := fun h => Finset.disjoint_left.1 hdisj h (Finset.mem_insert_self e T')
    have hdisj' : Disjoint C T' :=
      Finset.disjoint_of_subset_right (Finset.subset_insert e T') hdisj
    obtain ⟨Am, hAm, hmin⟩ := Finset.exists_min_image (insert e T').powerset
      (fun A => rank M₁.Indep (A ∪ C) + rank M₂.Indep ((insert e T' \ A) ∪ C))
      ⟨∅, Finset.empty_mem_powerset _⟩
    rw [Finset.mem_powerset] at hAm
    obtain ⟨J1, hJ1T, hJ1a, hJ1b, A1, hA1T, hA1⟩ := ih C hdisj' h1 h2
    by_cases hc : rank M₁.Indep (Am ∪ C) + rank M₂.Indep ((insert e T' \ Am) ∪ C)
        ≤ J1.card + 2 * C.card
    · exact ⟨J1, hJ1T.trans (Finset.subset_insert e T'), hJ1a, hJ1b, Am, hAm, hc⟩
    · rw [not_le] at hc
      have heA1 : e ∉ A1 := fun h => heT (hA1T h)
      have g1 := hmin A1 (Finset.mem_powerset.2 (hA1T.trans (Finset.subset_insert e T')))
      have g2 := hmin (insert e A1) (Finset.mem_powerset.2 (Finset.insert_subset_insert e hA1T))
      have eq1 : insert e T' \ A1 = insert e (T' \ A1) := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨hx | hx, hx'⟩
          · exact Or.inl hx
          · exact Or.inr ⟨hx, hx'⟩
        · rintro (hx | ⟨hx, hx'⟩)
          · subst hx; exact ⟨Or.inl rfl, heA1⟩
          · exact ⟨Or.inr hx, hx'⟩
      have eq2 : insert e T' \ insert e A1 = T' \ A1 := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨hx | hx, hx'⟩
          · exact absurd (Or.inl hx) hx'
          · exact ⟨hx, fun h => hx' (Or.inr h)⟩
        · rintro ⟨hx, hx'⟩
          refine ⟨Or.inr hx, ?_⟩
          rintro (h | h)
          · subst h; exact heT hx
          · exact hx' h
      rw [eq1, Finset.insert_union] at g1
      rw [eq2, Finset.insert_union] at g2
      have hi1 : M₁.Indep (insert e C) :=
        indep_insert_of_lt M₁ (X := A1 ∪ C) Finset.subset_union_right (by simp [heA1, heC]) h1 (by omega)
      have hi2 : M₂.Indep (insert e C) :=
        indep_insert_of_lt M₂ (X := (T' \ A1) ∪ C) Finset.subset_union_right (by simp [heC, heT]) h2 (by omega)
      have hdisj2 : Disjoint (insert e C) T' := Finset.disjoint_insert_left.2 ⟨heT, hdisj'⟩
      obtain ⟨J2, hJ2T, hJ2a, hJ2b, A2, hA2T, hA2⟩ := ih (insert e C) hdisj2 hi1 hi2
      have heJ2 : e ∉ J2 := fun h => heT (hJ2T h)
      have heA2 : e ∉ A2 := fun h => heT (hA2T h)
      have hJC : insert e J2 ∪ C = J2 ∪ insert e C := by
        rw [Finset.insert_union, Finset.union_insert]
      refine ⟨insert e J2, Finset.insert_subset_insert e hJ2T, hJC ▸ hJ2a, hJC ▸ hJ2b, Am, hAm,
        ?_⟩
      rw [Finset.card_insert_of_notMem heJ2]
      rw [Finset.card_insert_of_notMem heC] at hA2
      have s1 := rank_submod M₁ (A1 ∪ C) (A2 ∪ insert e C)
      have s2 := rank_submod M₂ ((T' \ A1) ∪ C) ((T' \ A2) ∪ insert e C)
      rw [setid1 heA1 heC, setid2] at s1
      rw [setid3 heT heC, setid4 heA1] at s2
      have g3 := hmin (A1 ∩ A2) (Finset.mem_powerset.2
        (Finset.inter_subset_left.trans (hA1T.trans (Finset.subset_insert e T'))))
      have g4 := hmin (insert e (A1 ∪ A2)) (Finset.mem_powerset.2
        (Finset.insert_subset_insert e (Finset.union_subset hA1T hA2T)))
      omega

end MIAux

open CombOpt.MatroidIntersection in
theorem solution {S : Type*} [Fintype S] [DecidableEq S] (M₁ M₂ : CombOpt.MatroidIntersection.Matroid S) :
    (∃ J A : Finset S, M₁.Indep J ∧ M₂.Indep J ∧
      J.card = rank M₁.Indep A + rank M₂.Indep Aᶜ) ∧
    ∀ J A : Finset S, M₁.Indep J → M₂.Indep J →
      J.card ≤ rank M₁.Indep A + rank M₂.Indep Aᶜ := by
  have weak : ∀ J A : Finset S, M₁.Indep J → M₂.Indep J →
      J.card ≤ rank M₁.Indep A + rank M₂.Indep Aᶜ := by
    intro J A h1 h2
    have hc := Finset.card_inter_add_card_sdiff J A
    have a := MIAux.card_le_rank M₁ (Finset.inter_subset_right : J ∩ A ⊆ A)
      (MIAux.indep_sub M₁ Finset.inter_subset_left h1)
    have b := MIAux.card_le_rank M₂
      (show J \ A ⊆ Aᶜ from fun x hx => by
        rw [Finset.mem_sdiff] at hx; rw [Finset.mem_compl]; exact hx.2)
      (MIAux.indep_sub M₂ Finset.sdiff_subset h2)
    omega
  refine ⟨?_, weak⟩
  obtain ⟨J, -, h1, h2, A, -, hA⟩ := MIAux.main M₁ M₂ Finset.univ ∅
    (Finset.disjoint_empty_left _) (MIAux.indep_empty M₁) (MIAux.indep_empty M₂)
  simp only [Finset.union_empty, Finset.card_empty, mul_zero, add_zero] at h1 h2 hA
  rw [← Finset.compl_eq_univ_sdiff] at hA
  exact ⟨J, A, h1, h2, le_antisymm (weak J A h1 h2) hA⟩

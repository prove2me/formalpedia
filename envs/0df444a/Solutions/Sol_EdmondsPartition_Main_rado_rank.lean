-- Prove2me | solution 1 for EdmondsPartition.Main.rado_rank
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T15:28:22.255428+00:00
-- url     : https://prove2.me/submissions/8966f649-7299-4041-ac59-1b55fde122ea

import Mathlib

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace EdmondsWork

open Finset

variable {ι β : Type*} [DecidableEq ι] [DecidableEq β]

/-- Hall's condition for the family `A` with respect to the rank function `r`. -/
def RHall (r : Finset β → ℤ) (A : ι → Finset β) : Prop :=
  ∀ J : Finset ι, (J.card : ℤ) ≤ r (J.biUnion A)

theorem biUnion_update_of_mem (A : ι → Finset β) (B : Finset β) {J : Finset ι} {i0 : ι}
    (h : i0 ∈ J) :
    J.biUnion (Function.update A i0 B) = (J.erase i0).biUnion A ∪ B := by
  conv_lhs => rw [← Finset.insert_erase h]
  rw [Finset.biUnion_insert, Function.update_self]
  have : (J.erase i0).biUnion (Function.update A i0 B) = (J.erase i0).biUnion A := by
    apply Finset.biUnion_congr rfl
    intro j hj
    exact Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
  rw [this, Finset.union_comm]

theorem biUnion_update_of_notMem (A : ι → Finset β) (B : Finset β) {J : Finset ι} {i0 : ι}
    (h : i0 ∉ J) :
    J.biUnion (Function.update A i0 B) = J.biUnion A := by
  apply Finset.biUnion_congr rfl
  intro j hj
  exact Function.update_of_ne (fun e => h (by subst e; exact hj)) _ _

theorem biUnion_mem_split (A : ι → Finset β) {J : Finset ι} {i0 : ι} (h : i0 ∈ J) :
    J.biUnion A = (J.erase i0).biUnion A ∪ A i0 := by
  conv_lhs => rw [← Finset.insert_erase h]
  rw [Finset.biUnion_insert, Finset.union_comm]

/-- The shrinking step of Rado's theorem: if `y ≠ z` both lie in `A i0`, deleting one of them
preserves Hall's condition. Only monotonicity and submodularity of `r` are used. -/
theorem rhall_shrink (r : Finset β → ℤ)
    (hmono : ∀ {X Y : Finset β}, X ⊆ Y → r X ≤ r Y)
    (hsub : ∀ X Y : Finset β, r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y)
    (A : ι → Finset β) (hA : RHall r A) {i0 : ι} {y z : β}
    (hy : y ∈ A i0) (hyz : y ≠ z) :
    RHall r (Function.update A i0 ((A i0).erase y)) ∨
      RHall r (Function.update A i0 ((A i0).erase z)) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  unfold RHall at h1 h2
  simp only [not_forall, not_le] at h1 h2
  obtain ⟨J1, hJ1⟩ := h1
  obtain ⟨J2, hJ2⟩ := h2
  have hi1 : i0 ∈ J1 := by
    by_contra hn
    rw [biUnion_update_of_notMem _ _ hn] at hJ1
    exact absurd (hA J1) (not_le.2 hJ1)
  have hi2 : i0 ∈ J2 := by
    by_contra hn
    rw [biUnion_update_of_notMem _ _ hn] at hJ2
    exact absurd (hA J2) (not_le.2 hJ2)
  rw [biUnion_update_of_mem _ _ hi1] at hJ1
  rw [biUnion_update_of_mem _ _ hi2] at hJ2
  set T1 := (J1.erase i0).biUnion A with hT1
  set T2 := (J2.erase i0).biUnion A with hT2
  set B := A i0 with hB
  have hPQ : (T1 ∪ B.erase y) ∪ (T2 ∪ B.erase z) = (J1 ∪ J2).biUnion A := by
    rw [biUnion_mem_split A (Finset.mem_union_left J2 hi1), Finset.erase_union_distrib,
      Finset.union_biUnion]
    ext x
    simp only [Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro ((h | ⟨_, h⟩) | (h | ⟨_, h⟩))
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · by_cases hxy : x = y
        · subst hxy
          exact Or.inr (Or.inr ⟨hyz, h⟩)
        · exact Or.inl (Or.inr ⟨hxy, h⟩)
  have hK : ((J1 ∩ J2).erase i0).biUnion A ⊆ (T1 ∪ B.erase y) ∩ (T2 ∪ B.erase z) := by
    intro x hx
    rw [Finset.mem_inter]
    constructor
    · refine Finset.mem_union_left _ ?_
      exact (Finset.biUnion_subset_biUnion_of_subset_left A
        (Finset.erase_subset_erase _ Finset.inter_subset_left)) hx
    · refine Finset.mem_union_left _ ?_
      exact (Finset.biUnion_subset_biUnion_of_subset_left A
        (Finset.erase_subset_erase _ Finset.inter_subset_right)) hx
  have hHall12 := hA (J1 ∪ J2)
  have hHallK := hA ((J1 ∩ J2).erase i0)
  have hsubm := hsub (T1 ∪ B.erase y) (T2 ∪ B.erase z)
  rw [hPQ] at hsubm
  have hmK := hmono hK
  have hcardK : (((J1 ∩ J2).erase i0).card : ℤ) = ((J1 ∩ J2).card : ℤ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_inter.2 ⟨hi1, hi2⟩)]
    have : 1 ≤ (J1 ∩ J2).card := Finset.card_pos.2 ⟨i0, Finset.mem_inter.2 ⟨hi1, hi2⟩⟩
    push_cast [Nat.cast_sub this]
    ring
  have hU := Finset.card_union_add_card_inter J1 J2
  have hU' : ((J1 ∪ J2).card : ℤ) + (J1 ∩ J2).card = J1.card + J2.card := by exact_mod_cast hU
  linarith


/-- Rado's theorem for a monotone submodular integer rank function `r` with `r X ≤ |X|`:
if every `J` satisfies `|J| ≤ r (⋃_{i ∈ J} A i)`, there is a choice `a i ∈ A i` whose image has
rank `|ι|`. -/
theorem rado_rank [Fintype ι] (r : Finset β → ℤ)
    (hmono : ∀ {X Y : Finset β}, X ⊆ Y → r X ≤ r Y)
    (hsub : ∀ X Y : Finset β, r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y)
    (hcard : ∀ X : Finset β, r X ≤ X.card)
    (A : ι → Finset β) (hA : RHall r A) :
    ∃ a : ι → β, (∀ i, a i ∈ A i) ∧ r (Finset.univ.image a) = Fintype.card ι := by
  suffices H : ∀ n : ℕ, ∀ A : ι → Finset β, RHall r A → ∑ i, (A i).card = n →
      ∃ a : ι → β, (∀ i, a i ∈ A i) ∧ r (Finset.univ.image a) = Fintype.card ι from
    H _ A hA rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hA hn
    by_cases hbig : ∃ i0, 1 < (A i0).card
    · obtain ⟨i0, hi0⟩ := hbig
      obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.1 hi0
      obtain ⟨w, hw, hH⟩ : ∃ w ∈ A i0, RHall r (Function.update A i0 ((A i0).erase w)) := by
        rcases rhall_shrink r hmono hsub A hA hy hyz with h | h
        · exact ⟨y, hy, h⟩
        · exact ⟨z, hz, h⟩
      have hle : ∀ j, (Function.update A i0 ((A i0).erase w) j).card ≤ (A j).card := by
        intro j
        by_cases hj : j = i0
        · subst hj; rw [Function.update_self]; exact Finset.card_erase_le
        · rw [Function.update_of_ne hj]
      have hlt : ∑ j, (Function.update A i0 ((A i0).erase w) j).card < ∑ j, (A j).card := by
        refine Finset.sum_lt_sum (fun j _ => hle j) ⟨i0, Finset.mem_univ _, ?_⟩
        rw [Function.update_self]
        exact Finset.card_erase_lt_of_mem hw
      obtain ⟨a, ha, hr⟩ := ih _ (hn ▸ hlt) _ hH rfl
      refine ⟨a, fun i => ?_, hr⟩
      have := ha i
      by_cases hj : i = i0
      · subst hj; rw [Function.update_self] at this; exact Finset.mem_of_mem_erase this
      · rwa [Function.update_of_ne hj] at this
    · push Not at hbig
      have hone : ∀ i, (A i).card = 1 := by
        intro i
        have h1 := hA {i}
        rw [Finset.singleton_biUnion] at h1
        have h2 := hcard (A i)
        have : 1 ≤ (A i).card := by
          have : (1 : ℤ) ≤ (A i).card := by simpa using h1.trans h2
          exact_mod_cast this
        exact le_antisymm (hbig i) this
      have hex : ∀ i, ∃ b, A i = {b} := fun i => Finset.card_eq_one.1 (hone i)
      choose a ha using hex
      refine ⟨a, fun i => by rw [ha i]; exact Finset.mem_singleton_self _, ?_⟩
      have hU : (Finset.univ : Finset ι).biUnion A = Finset.univ.image a := by
        ext x; simp [ha, eq_comm]
      have h1 := hA Finset.univ
      rw [hU] at h1
      have h2 := hcard (Finset.univ.image a)
      have h3 : ((Finset.univ.image a).card : ℤ) ≤ Fintype.card ι := by
        exact_mod_cast (Finset.card_image_le.trans (by simp))
      simp only [Finset.card_univ] at h1
      linarith

end EdmondsWork

theorem solution {ι β : Type*} [DecidableEq ι] [DecidableEq β] [Fintype ι]
    (r : Finset β → ℤ)
    (hmono : ∀ {X Y : Finset β}, X ⊆ Y → r X ≤ r Y)
    (hsub : ∀ X Y : Finset β, r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y)
    (hcard : ∀ X : Finset β, r X ≤ X.card)
    (A : ι → Finset β) (hA : ∀ J : Finset ι, (J.card : ℤ) ≤ r (J.biUnion A)) :
    ∃ a : ι → β, (∀ i, a i ∈ A i) ∧ r (Finset.univ.image a) = Fintype.card ι :=
  EdmondsWork.rado_rank r hmono hsub hcard A hA

#print axioms solution

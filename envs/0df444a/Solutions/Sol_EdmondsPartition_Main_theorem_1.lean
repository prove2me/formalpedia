-- Prove2me | solution 1 for EdmondsPartition.Main.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T16:01:50.000773+00:00
-- url     : https://prove2.me/submissions/c7196f4b-304b-4544-8d11-f300f23fd5b2

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic
import Theorems.Thm_EdmondsPartition_Main_partition_of_counting

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace EdmondsWork

open WhitneyMatroid.RankIndep EdmondsPartition.Main

variable {α : Type*} [DecidableEq α] {Indep : Finset α → Prop}

section
open Classical

/-- A set that is independent and inside `A` has at most `r(A)` elements. -/
theorem le_rank {I A : Finset α} (hIA : I ⊆ A) (hI : Indep I) :
    (I.card : ℤ) ≤ rankOfIndep Indep A := by
  unfold rankOfIndep
  exact_mod_cast Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hIA, hI⟩)

/-- With `∅` independent, some independent subset of `A` attains `r(A)`. -/
theorem exists_indep_card_eq_rank (h0 : Indep ∅) (A : Finset α) :
    ∃ I, I ⊆ A ∧ Indep I ∧ (I.card : ℤ) = rankOfIndep Indep A := by
  have hne : (A.powerset.filter Indep).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset A, h0⟩⟩
  obtain ⟨I, hI, hIeq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  obtain ⟨hIA, hIi⟩ := Finset.mem_filter.1 hI
  exact ⟨I, Finset.mem_powerset.1 hIA, hIi, by unfold rankOfIndep; exact_mod_cast hIeq.symm⟩

end

theorem rank_nonneg (A : Finset α) : 0 ≤ rankOfIndep Indep A := by
  classical
  unfold rankOfIndep
  exact_mod_cast Nat.zero_le _

/-- Every independent `I ⊆ A` extends to an independent `J` with `I ⊆ J ⊆ A` and `|J| = r(A)`,
using Axiom 2. -/
theorem exists_extension_card_eq_rank (h2 : Axiom2 Indep) (h0 : Indep ∅)
    {I A : Finset α} (hIA : I ⊆ A) (hI : Indep I) :
    ∃ J, I ⊆ J ∧ J ⊆ A ∧ Indep J ∧ (J.card : ℤ) = rankOfIndep Indep A := by
  classical
  -- a maximal-cardinality independent set between `I` and `A`
  have hmax : ∀ I' : Finset α, I' ⊆ A → Indep I' →
      ∃ J, I' ⊆ J ∧ IsMaxIndepIn Indep A J := by
    intro I' hI'A hI'
    have hne : (A.powerset.filter (fun J => I' ⊆ J ∧ Indep J)).Nonempty :=
      ⟨I', Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hI'A, Finset.Subset.refl _, hI'⟩⟩
    obtain ⟨J, hJ, hJmax⟩ := Finset.exists_max_image _ Finset.card hne
    obtain ⟨hJA, hIJ, hJi⟩ := Finset.mem_filter.1 hJ
    refine ⟨J, hIJ, Finset.mem_powerset.1 hJA, hJi, ?_⟩
    intro K hJK hKA hKi
    have hK : K ∈ A.powerset.filter (fun J => I' ⊆ J ∧ Indep J) :=
      Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hKA, hIJ.trans hJK, hKi⟩
    exact (Finset.eq_of_subset_of_card_le hJK (hJmax K hK)).symm
  obtain ⟨J, hIJ, hJmaxA⟩ := hmax I hIA hI
  obtain ⟨I0, hI0A, hI0i, hI0card⟩ := exists_indep_card_eq_rank h0 (Indep := Indep) A
  obtain ⟨M, hI0M, hMmax⟩ := hmax I0 hI0A hI0i
  have hMle : (M.card : ℤ) ≤ rankOfIndep Indep A := le_rank hMmax.1 hMmax.2.1
  have hMge : (I0.card : ℤ) ≤ M.card := by exact_mod_cast Finset.card_le_card hI0M
  have hMeq : (M.card : ℤ) = rankOfIndep Indep A := le_antisymm hMle (hI0card ▸ hMge)
  have hJM : J.card = M.card := h2 A J M hJmaxA hMmax
  exact ⟨J, hIJ, hJmaxA.1, hJmaxA.2.1, by rw [hJM]; exact hMeq⟩

theorem rank_mono (h0 : Indep ∅) {A B : Finset α} (hAB : A ⊆ B) :
    rankOfIndep Indep A ≤ rankOfIndep Indep B := by
  obtain ⟨I, hIA, hIi, hIc⟩ := exists_indep_card_eq_rank h0 (Indep := Indep) A
  rw [← hIc]
  exact le_rank (hIA.trans hAB) hIi

theorem rank_le_card (h0 : Indep ∅) (A : Finset α) :
    rankOfIndep Indep A ≤ (A.card : ℤ) := by
  obtain ⟨I, hIA, _, hIc⟩ := exists_indep_card_eq_rank h0 (Indep := Indep) A
  rw [← hIc]
  exact_mod_cast Finset.card_le_card hIA

theorem rank_of_indep (h0 : Indep ∅) {I : Finset α} (hI : Indep I) :
    rankOfIndep Indep I = (I.card : ℤ) :=
  le_antisymm (rank_le_card h0 I) (le_rank (Finset.Subset.refl I) hI)

theorem indep_of_rank_eq_card (h0 : Indep ∅) {A : Finset α}
    (h : rankOfIndep Indep A = (A.card : ℤ)) : Indep A := by
  obtain ⟨I, hIA, hIi, hIc⟩ := exists_indep_card_eq_rank h0 (Indep := Indep) A
  have : I = A :=
    Finset.eq_of_subset_of_card_le hIA (by rw [← Nat.cast_le (α := ℤ), hIc, h])
  exact this ▸ hIi

/-- Submodularity of the rank. -/
theorem rank_submod (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) (A B : Finset α) :
    rankOfIndep Indep (A ∪ B) + rankOfIndep Indep (A ∩ B) ≤
      rankOfIndep Indep A + rankOfIndep Indep B := by
  obtain ⟨K, hKAB, hKi, hKc⟩ := exists_indep_card_eq_rank h0 (Indep := Indep) (A ∩ B)
  have hKsub : K ⊆ A ∪ B := hKAB.trans (Finset.inter_subset_left.trans Finset.subset_union_left)
  obtain ⟨L, hKL, hLAB, hLi, hLc⟩ := exists_extension_card_eq_rank h2 h0 hKsub hKi
  have hLA : ((L ∩ A).card : ℤ) ≤ rankOfIndep Indep A :=
    le_rank Finset.inter_subset_right (h1 _ _ Finset.inter_subset_left hLi)
  have hLB : ((L ∩ B).card : ℤ) ≤ rankOfIndep Indep B :=
    le_rank Finset.inter_subset_right (h1 _ _ Finset.inter_subset_left hLi)
  have hcard := Finset.card_union_add_card_inter (L ∩ A) (L ∩ B)
  have hunion : L ∩ A ∪ L ∩ B = L := by
    rw [← Finset.inter_union_distrib_left]; exact Finset.inter_eq_left.2 hLAB
  have hKsub2 : K ⊆ (L ∩ A) ∩ (L ∩ B) := by
    intro x hx
    have hxL := hKL hx
    have hxAB := Finset.mem_inter.1 (hKAB hx)
    simp [hxL, hxAB.1, hxAB.2]
  have hKle : K.card ≤ ((L ∩ A) ∩ (L ∩ B)).card := Finset.card_le_card hKsub2
  rw [hunion] at hcard
  have : (L.card : ℤ) + K.card ≤ (L ∩ A).card + (L ∩ B).card := by
    have h' : (L.card : ℤ) + ((L ∩ A) ∩ (L ∩ B)).card = (L ∩ A).card + (L ∩ B).card := by
      exact_mod_cast hcard
    have : (K.card : ℤ) ≤ ((L ∩ A) ∩ (L ∩ B)).card := by exact_mod_cast hKle
    linarith
  linarith

end EdmondsWork

namespace EdmondsWork

open WhitneyMatroid.RankIndep EdmondsPartition.Main

theorem only_if_part {α : Type*} [Fintype α] [DecidableEq α] (Indep : Finset α → Prop)
    (h1 : IndepI1 Indep) :
    ∀ (k : ℕ) (I : Fin k → Finset α), IsPartitionInto Indep k I →
      ∀ A : Finset α, (A.card : ℤ) ≤ (k : ℤ) * rankOfIndep Indep A := by
  intro k I hI A
  obtain ⟨hind, _, hcover⟩ := hI
  have hsub : A ⊆ Finset.univ.biUnion (fun i => A ∩ I i) := by
    intro a ha
    have : a ∈ Finset.univ.biUnion I := by rw [hcover]; exact Finset.mem_univ a
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 this
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_inter.2 ⟨ha, hi⟩⟩
  have h1' : A.card ≤ ∑ i : Fin k, (A ∩ I i).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∀ i : Fin k, ((A ∩ I i).card : ℤ) ≤ rankOfIndep Indep A := fun i =>
    le_rank Finset.inter_subset_left (h1 _ _ Finset.inter_subset_right (hind i))
  calc (A.card : ℤ) ≤ ∑ i : Fin k, ((A ∩ I i).card : ℤ) := by exact_mod_cast h1'
    _ ≤ ∑ _i : Fin k, rankOfIndep Indep A := Finset.sum_le_sum fun i _ => h2 i
    _ = (k : ℤ) * rankOfIndep Indep A := by simp

end EdmondsWork

open WhitneyMatroid.RankIndep EdmondsPartition.Main

theorem solution {α : Type*} [Fintype α] [DecidableEq α] (Indep : Finset α → Prop)
    (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) (k : ℕ) :
    (∃ I : Fin k → Finset α, IsPartitionInto Indep k I) ↔
      ¬ ∃ A : Finset α, (k : ℤ) * rankOfIndep Indep A < (A.card : ℤ) :=
  by
  constructor
  · rintro ⟨I, hI⟩ ⟨A, hA⟩
    exact absurd (EdmondsWork.only_if_part Indep h1 k I hI A) (not_le.2 hA)
  · intro h
    obtain ⟨I, hi, hd, hu⟩ := partition_of_counting Indep h1 h2 h0 k Finset.univ
      (fun J _ => not_lt.1 fun hlt => h ⟨J, hlt⟩)
    exact ⟨I, hi, hd, hu⟩

#print axioms solution

-- Prove2me | solution 1 for EdmondsPartition.Main.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T16:01:56.442231+00:00
-- url     : https://prove2.me/submissions/a383711c-5eba-4bb8-b97e-8e6450d287c2

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic
import Theorems.Thm_EdmondsPartition_Main_span_facts

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

variable {α : Type*} [DecidableEq α] {Indep : Finset α → Prop}

/-- A dependent set contains a circuit. -/
theorem exists_circuit_subset {D : Finset α} (hD : ¬ Indep D) :
    ∃ C, C ⊆ D ∧ IsCircuit Indep C := by
  classical
  have hne : (D.powerset.filter (fun C => ¬ Indep C)).Nonempty :=
    ⟨D, Finset.mem_filter.2 ⟨Finset.mem_powerset_self D, hD⟩⟩
  obtain ⟨C, hCmin⟩ := Finset.exists_minimal hne
  obtain ⟨hCD, hCd⟩ := Finset.mem_filter.1 hCmin.1
  refine ⟨C, Finset.mem_powerset.1 hCD, hCd, fun E hE => ?_⟩
  by_contra hEi
  have hE' : E ∈ D.powerset.filter (fun C => ¬ Indep C) :=
    Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (hE.subset.trans (Finset.mem_powerset.1 hCD)), hEi⟩
  exact (Finset.ssubset_def.1 hE).2 (hCmin.2 hE' hE.subset)

theorem indep_erase_of_circuit {C : Finset α} (hC : IsCircuit Indep C) {e : α} (he : e ∈ C) :
    Indep (C.erase e) := hC.2 _ (Finset.erase_ssubset he)

/-- A circuit has rank one less than its size, and equals the rank of any of its one-point
deletions. -/
theorem rank_circuit_erase (h0 : Indep ∅) {C : Finset α} (hC : IsCircuit Indep C) {e : α}
    (he : e ∈ C) : rankOfIndep Indep C = rankOfIndep Indep (C.erase e) := by
  have hI := indep_erase_of_circuit hC he
  have h1 : rankOfIndep Indep (C.erase e) = ((C.erase e).card : ℤ) := rank_of_indep h0 hI
  have h2 : rankOfIndep Indep (C.erase e) ≤ rankOfIndep Indep C :=
    rank_mono h0 (Finset.erase_subset e C)
  have h3 : rankOfIndep Indep C ≤ (C.card : ℤ) := rank_le_card h0 C
  have h4 : rankOfIndep Indep C ≠ (C.card : ℤ) := fun h => hC.1 (indep_of_rank_eq_card h0 h)
  have h5 : (C.erase e).card + 1 = C.card := Finset.card_erase_add_one he
  have : (C.card : ℤ) = ((C.erase e).card : ℤ) + 1 := by exact_mod_cast h5.symm
  omega

/-- If adding `e` does not raise the rank of `J` and `e ∉ J`, then `e` lies on a circuit inside
`J + e`. -/
theorem exists_circuit_of_rank_eq (h1 : IndepI1 Indep) (h0 : Indep ∅) {J : Finset α} {e : α}
    (hr : rankOfIndep Indep (insert e J) = rankOfIndep Indep J) (heJ : e ∉ J) :
    ∃ C, IsCircuit Indep C ∧ e ∈ C ∧ C ⊆ insert e J := by
  obtain ⟨I, hIJ, hIi, hIc⟩ := exists_indep_card_eq_rank h0 (Indep := Indep) J
  have heI : e ∉ I := fun h => heJ (hIJ h)
  have hdep : ¬ Indep (insert e I) := by
    intro hi
    have := le_rank (Finset.insert_subset_insert e hIJ) hi
    rw [Finset.card_insert_of_notMem heI] at this
    push_cast at this
    linarith
  obtain ⟨C, hCs, hC⟩ := exists_circuit_subset hdep
  have heC : e ∈ C := by
    by_contra hn
    have hCI : C ⊆ I := by
      intro x hx
      rcases Finset.mem_insert.1 (hCs hx) with rfl | h
      · exact absurd hx hn
      · exact h
    exact hC.1 (h1 _ _ hCI hIi)
  exact ⟨C, hC, heC, hCs.trans (Finset.insert_subset_insert e hIJ)⟩

end EdmondsWork

open WhitneyMatroid.RankIndep EdmondsPartition.Main

theorem solution {α : Type*} [Fintype α] [DecidableEq α] (Indep : Finset α → Prop)
    (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) :
    ∀ (A : Finset α) (e : α),
      e ∈ spanOf Indep A ↔ e ∈ A ∨ ∃ C : Finset α, IsCircuit Indep C ∧ C \ A = {e} :=
  by
  classical
  intro A e
  obtain ⟨ha, hb, _⟩ := span_facts Indep h1 h2 h0 A
  have hAsub : A ⊆ spanOf Indep A := fun x hx => (ha x).2 (by rw [Finset.insert_eq_of_mem hx])
  constructor
  · intro he
    by_cases heA : e ∈ A
    · exact Or.inl heA
    · obtain ⟨C, hC, heC, hCs⟩ := EdmondsWork.exists_circuit_of_rank_eq h1 h0 ((ha e).1 he) heA
      refine Or.inr ⟨C, hC, ?_⟩
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · rintro ⟨hxC, hxA⟩
        rcases Finset.mem_insert.1 (hCs hxC) with h | h
        · exact h
        · exact absurd h hxA
      · rintro rfl
        exact ⟨heC, heA⟩
  · rintro (heA | ⟨C, hC, hCA⟩)
    · exact hAsub heA
    · by_contra hne
      refine hb C hC ?_
      have heC : e ∈ C := (Finset.mem_sdiff.1 (hCA ▸ Finset.mem_singleton_self e)).1
      have : C \ spanOf Indep A = {e} := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · rintro ⟨hxC, hxS⟩
          have : x ∈ C \ A := Finset.mem_sdiff.2 ⟨hxC, fun hxA => hxS (hAsub hxA)⟩
          rw [hCA] at this
          exact Finset.mem_singleton.1 this
        · rintro rfl
          exact ⟨heC, hne⟩
      rw [this]; simp

#print axioms solution

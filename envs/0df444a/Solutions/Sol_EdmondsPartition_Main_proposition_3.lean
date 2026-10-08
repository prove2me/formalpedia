-- Prove2me | solution 1 for EdmondsPartition.Main.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T16:01:54.654489+00:00
-- url     : https://prove2.me/submissions/d08b888d-c6d5-4714-ac34-599e915ce9d3

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic

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

namespace EdmondsWork

open WhitneyMatroid.RankIndep EdmondsPartition.Main

variable {α : Type*} [DecidableEq α] {Indep : Finset α → Prop}

variable [Fintype α]

/-- The rank closure of `J`: the elements that do not raise its rank. -/
noncomputable def clos (Indep : Finset α → Prop) (J : Finset α) : Finset α :=
  Finset.univ.filter (fun e => rankOfIndep Indep (insert e J) = rankOfIndep Indep J)

theorem mem_clos {J : Finset α} {e : α} :
    e ∈ clos Indep J ↔ rankOfIndep Indep (insert e J) = rankOfIndep Indep J := by
  simp [clos]

theorem subset_clos (J : Finset α) : J ⊆ clos Indep J := fun e he => by
  rw [mem_clos, Finset.insert_eq_of_mem he]

theorem rank_union_eq_of_subset_clos (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅)
    {J B : Finset α} (hB : B ⊆ clos Indep J) :
    rankOfIndep Indep (J ∪ B) = rankOfIndep Indep J := by
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B' hb ih =>
    have hB' : B' ⊆ clos Indep J := (Finset.subset_insert b B').trans hB
    have hbJ : b ∈ clos Indep J := hB (Finset.mem_insert_self b B')
    have ih' := ih hB'
    have hsub := rank_submod h1 h2 h0 (J ∪ B') (insert b J)
    have hU : (J ∪ B') ∪ insert b J = J ∪ insert b B' := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    have hmono : rankOfIndep Indep J ≤ rankOfIndep Indep ((J ∪ B') ∩ insert b J) :=
      rank_mono h0 (fun x hx => Finset.mem_inter.2
        ⟨Finset.mem_union_left _ hx, Finset.mem_insert_of_mem hx⟩)
    have hbr := mem_clos.1 hbJ
    rw [hU] at hsub
    have hge : rankOfIndep Indep J ≤ rankOfIndep Indep (J ∪ insert b B') :=
      rank_mono h0 Finset.subset_union_left
    linarith

theorem rank_clos (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) (J : Finset α) :
    rankOfIndep Indep (clos Indep J) = rankOfIndep Indep J := by
  have := rank_union_eq_of_subset_clos h1 h2 h0 (Finset.Subset.refl (clos Indep J)) (J := J)
  rwa [Finset.union_eq_right.2 (subset_clos J)] at this

/-- If a circuit `C` has all but `e` in the closure side `J ∪ C.erase e`, then `e` joins the closure. -/
theorem circuit_closes (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) {C : Finset α}
    (hC : IsCircuit Indep C) {e : α} (he : e ∈ C) (J : Finset α) :
    e ∈ clos Indep (J ∪ C.erase e) := by
  rw [mem_clos]
  have hsub := rank_submod h1 h2 h0 (J ∪ C.erase e) C
  have hU : (J ∪ C.erase e) ∪ C = insert e (J ∪ C.erase e) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ((h | ⟨_, h⟩) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨‹_›, h⟩)
      · by_cases hx : x = e
        · exact Or.inl hx
        · exact Or.inr (Or.inr ⟨hx, h⟩)
    · rintro (h | h | h)
      · exact Or.inr (h ▸ he)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
  have hm : rankOfIndep Indep (C.erase e) ≤ rankOfIndep Indep ((J ∪ C.erase e) ∩ C) :=
    rank_mono h0 (fun x hx => Finset.mem_inter.2
      ⟨Finset.mem_union_right _ hx, Finset.mem_of_mem_erase hx⟩)
  have hc := rank_circuit_erase h0 hC he
  rw [hU] at hsub
  have hge : rankOfIndep Indep (J ∪ C.erase e) ≤ rankOfIndep Indep (insert e (J ∪ C.erase e)) :=
    rank_mono h0 (Finset.subset_insert _ _)
  linarith

theorem clos_subset_of_subset_clos (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅)
    {Z B : Finset α} (hB : B ⊆ clos Indep Z) : clos Indep B ⊆ clos Indep Z := by
  intro e he
  rw [mem_clos] at he ⊢
  have hZB := rank_union_eq_of_subset_clos h1 h2 h0 hB
  have hsub := rank_submod h1 h2 h0 (Z ∪ B) (insert e B)
  have hU : (Z ∪ B) ∪ insert e B = insert e (Z ∪ B) := by
    ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
  have hm : rankOfIndep Indep B ≤ rankOfIndep Indep ((Z ∪ B) ∩ insert e B) :=
    rank_mono h0 (fun x hx => Finset.mem_inter.2
      ⟨Finset.mem_union_right _ hx, Finset.mem_insert_of_mem hx⟩)
  rw [hU] at hsub
  have hle : rankOfIndep Indep (insert e Z) ≤ rankOfIndep Indep (insert e (Z ∪ B)) :=
    rank_mono h0 (Finset.insert_subset_insert e Finset.subset_union_left)
  have hge : rankOfIndep Indep Z ≤ rankOfIndep Indep (insert e Z) :=
    rank_mono h0 (Finset.subset_insert e Z)
  linarith

theorem isSpan_clos (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) (J : Finset α) :
    IsSpan Indep (clos Indep J) := by
  intro C hC hcard
  obtain ⟨e, he⟩ := Finset.card_eq_one.1 hcard
  have heC : e ∈ C := (Finset.mem_sdiff.1 (he ▸ Finset.mem_singleton_self e)).1
  have hen : e ∉ clos Indep J := (Finset.mem_sdiff.1 (he ▸ Finset.mem_singleton_self e)).2
  have hrest : C.erase e ⊆ clos Indep J := by
    intro x hx
    by_contra hxn
    have : x ∈ C \ clos Indep J := Finset.mem_sdiff.2 ⟨Finset.mem_of_mem_erase hx, hxn⟩
    rw [he] at this
    exact (Finset.ne_of_mem_erase hx) (Finset.mem_singleton.1 this)
  have hr := rank_union_eq_of_subset_clos h1 h2 h0 hrest
  have hcl := mem_clos.1 (circuit_closes h1 h2 h0 hC heC J)
  have hle : rankOfIndep Indep (insert e J) ≤ rankOfIndep Indep (insert e (J ∪ C.erase e)) :=
    rank_mono h0 (Finset.insert_subset_insert e Finset.subset_union_left)
  have hge : rankOfIndep Indep J ≤ rankOfIndep Indep (insert e J) :=
    rank_mono h0 (Finset.subset_insert e J)
  exact hen (mem_clos.2 (by linarith))

/-- An element of the closure outside `J` lies on a circuit inside `J + e`. -/
theorem exists_circuit_of_mem_clos (h1 : IndepI1 Indep) (h0 : Indep ∅) {J : Finset α} {e : α}
    (he : e ∈ clos Indep J) (heJ : e ∉ J) :
    ∃ C, IsCircuit Indep C ∧ e ∈ C ∧ C ⊆ insert e J :=
  exists_circuit_of_rank_eq h1 h0 (mem_clos.1 he) heJ

theorem clos_subset_of_isSpan (h1 : IndepI1 Indep) (h0 : Indep ∅) {S J : Finset α}
    (hS : IsSpan Indep S) (hJS : J ⊆ S) : clos Indep J ⊆ S := by
  intro e he
  by_contra heS
  have heJ : e ∉ J := fun h => heS (hJS h)
  obtain ⟨C, hC, heC, hCs⟩ := exists_circuit_of_mem_clos h1 h0 he heJ
  apply hS C hC
  have : C \ S = {e} := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨hxC, hxS⟩
      by_contra hxe
      rcases Finset.mem_insert.1 (hCs hxC) with h | h
      · exact hxe h
      · exact hxS (hJS h)
    · rintro rfl
      exact ⟨heC, heS⟩
  rw [this]; simp

theorem spanOf_eq_clos (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) (J : Finset α) :
    spanOf Indep J = clos Indep J := by
  classical
  unfold spanOf
  apply le_antisymm
  · exact Finset.inf_le (f := id)
      (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _), subset_clos J,
        isSpan_clos h1 h2 h0 J⟩)
  · refine Finset.le_inf fun S hS => ?_
    obtain ⟨hJS, hspan⟩ := (Finset.mem_filter.1 hS).2
    exact clos_subset_of_isSpan h1 h0 hspan hJS

/-- From the span hypothesis, the counting inequality holds for every set. -/
theorem card_le_mul_rank_of_spans (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) (k : ℕ)
    (hspan : ∀ S : Finset α, IsSpan Indep S → (S.card : ℤ) ≤ (k : ℤ) * rankOfIndep Indep S)
    (J : Finset α) : (J.card : ℤ) ≤ (k : ℤ) * rankOfIndep Indep J := by
  calc (J.card : ℤ) ≤ (clos Indep J).card := by exact_mod_cast Finset.card_le_card (subset_clos J)
    _ ≤ (k : ℤ) * rankOfIndep Indep (clos Indep J) := hspan _ (isSpan_clos h1 h2 h0 J)
    _ = (k : ℤ) * rankOfIndep Indep J := by rw [rank_clos h1 h2 h0]

/-- The closure facts about `spanOf` that the partition theorem needs. -/
theorem span_facts (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) (J : Finset α) :
    (∀ e : α, e ∈ spanOf Indep J ↔ rankOfIndep Indep (insert e J) = rankOfIndep Indep J) ∧
      IsSpan Indep (spanOf Indep J) ∧
      rankOfIndep Indep (spanOf Indep J) = rankOfIndep Indep J := by
  rw [spanOf_eq_clos h1 h2 h0]
  exact ⟨fun e => mem_clos, isSpan_clos h1 h2 h0 J, rank_clos h1 h2 h0 J⟩

end EdmondsWork

namespace EdmondsWork

open WhitneyMatroid.RankIndep EdmondsPartition.Main

variable {α : Type*} [DecidableEq α] {Indep : Finset α → Prop}

theorem axiom1c_isCircuit : Axiom1c (IsCircuit Indep) := by
  intro C1 C2 hC1 hC2 hsub
  by_contra hne
  exact hC1.1 (hC2.2 C1 (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩))

theorem axiom2c_of_axiom2' (h2' : Axiom2' Indep) : Axiom2c (IsCircuit Indep) := by
  intro C1 C2 e hC1 hC2 hne he1 he2
  by_contra hno
  push Not at hno
  have hD : Indep ((C1 ∪ C2).erase e) := by
    by_contra hd
    obtain ⟨C, hCs, hC⟩ := exists_circuit_subset hd
    exact hno C hC hCs
  have hs : ∀ C : Finset α, C ⊆ C1 ∪ C2 → C ⊆ insert e ((C1 ∪ C2).erase e) := by
    intro C hC x hx
    by_cases hxe : x = e
    · exact Finset.mem_insert.2 (Or.inl hxe)
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hxe, hC hx⟩)
  exact hne (h2' _ e hD C1 C2 hC1 hC2 (hs C1 Finset.subset_union_left)
    (hs C2 Finset.subset_union_right))

/-- A circuit inside `insert e I` (`I` independent) contains `e`. -/
theorem mem_of_circuit_subset_insert (h1 : IndepI1 Indep) {I C : Finset α} {e : α}
    (hI : Indep I) (hC : IsCircuit Indep C) (hCs : C ⊆ insert e I) : e ∈ C := by
  by_contra hn
  have hCI : C ⊆ I := by
    intro x hx
    rcases Finset.mem_insert.1 (hCs hx) with rfl | h
    · exact absurd hx hn
    · exact h
  exact hC.1 (h1 _ _ hCI hI)

/-- (Axiom 1 and Axiom 2) imply Axiom 2'. -/
theorem axiom2'_of_axiom2 [Fintype α] (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) :
    Axiom2' Indep := by
  intro I e hI C1 C2 hC1 hC2 hs1 hs2
  have h0 : Indep ∅ := h1 _ _ (Finset.empty_subset I) hI
  by_contra hne
  have he1 := mem_of_circuit_subset_insert h1 hI hC1 hs1
  have he2 := mem_of_circuit_subset_insert h1 hI hC2 hs2
  have heI : e ∉ I := fun h => hC1.1 (h1 _ _ (by
    intro x hx; rcases Finset.mem_insert.1 (hs1 hx) with rfl | h'
    · exact h
    · exact h') hI)
  -- an element of `C1` outside `C2`
  obtain ⟨a, haC1, haC2⟩ : ∃ a ∈ C1, a ∉ C2 := by
    by_contra hall
    push Not at hall
    exact hne (axiom1c_isCircuit C1 C2 hC1 hC2 hall)
  have hae : a ≠ e := fun h => haC2 (h ▸ he2)
  have haA : a ∈ insert e I := hs1 haC1
  have hI' : Indep (C1.erase a) := hC1.2 _ (Finset.erase_ssubset haC1)
  obtain ⟨M, hIM, hMA, hMi, hMc⟩ := exists_extension_card_eq_rank h2 h0
    ((Finset.erase_subset a C1).trans hs1) hI'
  -- `|M| = |I|`
  have hMle : M.card ≤ I.card := by
    by_contra hlt
    push Not at hlt
    have hcard : (insert e I).card = I.card + 1 := Finset.card_insert_of_notMem heI
    have hMeq : M = insert e I :=
      Finset.eq_of_subset_of_card_le hMA (by omega)
    exact hC1.1 (h1 _ _ hs1 (hMeq ▸ hMi))
  have hMge : I.card ≤ M.card := by
    have := le_rank (Finset.Subset.refl I |>.trans (Finset.subset_insert e I)) hI
    have h' : (I.card : ℤ) ≤ M.card := by rw [hMc]; exact this
    exact_mod_cast h'
  have heM : e ∈ M := hIM (Finset.mem_erase.2 ⟨hae.symm, he1⟩)
  have haM : a ∉ M := by
    intro ha
    have : C1 ⊆ M := by
      intro x hx
      by_cases hxa : x = a
      · exact hxa ▸ ha
      · exact hIM (Finset.mem_erase.2 ⟨hxa, hx⟩)
    exact hC1.1 (h1 _ _ this hMi)
  have hMsub : M ⊆ (insert e I).erase a := fun x hx =>
    Finset.mem_erase.2 ⟨fun h => haM (h ▸ hx), hMA hx⟩
  have hcardA : ((insert e I).erase a).card = I.card := by
    have h' : ((insert e I).erase a).card + 1 = (insert e I).card := Finset.card_erase_add_one haA
    have : (insert e I).card = I.card + 1 := Finset.card_insert_of_notMem heI
    omega
  have hMeq : M = (insert e I).erase a :=
    Finset.eq_of_subset_of_card_le hMsub (by omega)
  have hC2sub : C2 ⊆ (insert e I).erase a := fun x hx =>
    Finset.mem_erase.2 ⟨fun h => haC2 (h ▸ hx), hs2 hx⟩
  exact hC2.1 (h1 _ _ (hMeq ▸ hC2sub) hMi)

/-- Augmentation from Axiom 2'. -/
theorem augmentation_of_axiom2' (h1 : IndepI1 Indep) (h2' : Axiom2' Indep) (J : Finset α)
    (hJ : Indep J) :
    ∀ (n : ℕ) (I : Finset α), (I \ J).card = n → Indep I → I.card < J.card →
      ∃ x ∈ J, x ∉ I ∧ Indep (insert x I) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro I hn hI hcard
    by_contra hno
    push Not at hno
    obtain ⟨x, hxJ, hxI⟩ : ∃ x ∈ J, x ∉ I := by
      by_contra hall
      push Not at hall
      exact absurd (Finset.card_le_card hall) (not_le.2 hcard)
    have hdep := hno x hxJ hxI
    obtain ⟨C, hCs, hC⟩ := exists_circuit_subset hdep
    have hxC := mem_of_circuit_subset_insert h1 hI hC hCs
    obtain ⟨y, hyC, hyJ⟩ : ∃ y ∈ C, y ∉ J := by
      by_contra hall
      push Not at hall
      exact hC.1 (h1 _ _ hall hJ)
    have hyx : y ≠ x := fun h => hyJ (h ▸ hxJ)
    have hyI : y ∈ I := by
      rcases Finset.mem_insert.1 (hCs hyC) with h | h
      · exact absurd h hyx
      · exact h
    set I' := insert x (I.erase y) with hI'
    have hxe : x ∉ I.erase y := fun h => hxI (Finset.mem_of_mem_erase h)
    have hIsub : I' ⊆ insert x I := Finset.insert_subset_insert x (Finset.erase_subset y I)
    have hI'i : Indep I' := by
      by_contra hd
      obtain ⟨C', hC's, hC'⟩ := exists_circuit_subset hd
      have := h2' I x hI C' C hC' hC (hC's.trans hIsub) hCs
      have hyI' : y ∈ I' := hC's (this ▸ hyC)
      rcases Finset.mem_insert.1 hyI' with h | h
      · exact hyx h
      · exact (Finset.notMem_erase y I) h
    have hcI' : I'.card = I.card := by
      rw [hI', Finset.card_insert_of_notMem hxe, Finset.card_erase_of_mem hyI]
      have : 1 ≤ I.card := Finset.card_pos.2 ⟨y, hyI⟩
      omega
    have hdiff : (I' \ J).card < n := by
      have : I' \ J = (I \ J).erase y := by
        ext z
        simp only [hI', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨h | ⟨hzy, hzI⟩, hzJ⟩
          · exact absurd (h ▸ hxJ) hzJ
          · exact ⟨hzy, hzI, hzJ⟩
        · rintro ⟨hzy, hzI, hzJ⟩
          exact ⟨Or.inr ⟨hzy, hzI⟩, hzJ⟩
      rw [this, ← hn]
      exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.2 ⟨hyI, hyJ⟩)
    obtain ⟨x', hx'J, hx'I', hx'i⟩ := ih _ hdiff I' rfl hI'i (by omega)
    have hx'y : x' ≠ y := fun h => hyJ (h ▸ hx'J)
    have hx'x : x' ≠ x := fun h => hx'I' (Finset.mem_insert.2 (Or.inl h))
    have hx'I : x' ∉ I := fun h =>
      hx'I' (Finset.mem_insert.2 (Or.inr (Finset.mem_erase.2 ⟨hx'y, h⟩)))
    have hdep' := hno x' hx'J hx'I
    obtain ⟨C'', hC''s, hC''⟩ := exists_circuit_subset hdep'
    have hx'C'' := mem_of_circuit_subset_insert h1 hI hC'' hC''s
    have hyC'' : y ∈ C'' := by
      by_contra hn'
      apply hC''.1
      refine h1 _ _ ?_ hx'i
      intro z hz
      rcases Finset.mem_insert.1 (hC''s hz) with h | h
      · exact Finset.mem_insert.2 (Or.inl h)
      · refine Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2 (Or.inr
          (Finset.mem_erase.2 ⟨fun hzy => hn' (hzy ▸ hz), h⟩))))
    have hCne : C ≠ C'' := by
      intro h
      have := hC''s (h ▸ hxC)
      rcases Finset.mem_insert.1 this with h' | h'
      · exact hx'x h'.symm
      · exact hxI h'
    obtain ⟨D, hD, hDs⟩ := axiom2c_of_axiom2' h2' C C'' y hC hC'' hCne hyC hyC''
    apply hD.1
    refine h1 _ _ ?_ hx'i
    intro z hz
    obtain ⟨hzy, hz'⟩ := Finset.mem_erase.1 (hDs hz)
    show z ∈ insert x' (insert x (I.erase y))
    rcases Finset.mem_union.1 hz' with h | h
    · rcases Finset.mem_insert.1 (hCs h) with h' | h'
      · exact Finset.mem_insert_of_mem (Finset.mem_insert.2 (Or.inl h'))
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hzy, h'⟩))
    · rcases Finset.mem_insert.1 (hC''s h) with h' | h'
      · exact Finset.mem_insert.2 (Or.inl h')
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hzy, h'⟩))

theorem axiom2_of_axiom2' (h1 : IndepI1 Indep) (h2' : Axiom2' Indep) : Axiom2 Indep := by
  intro A I J hI hJ
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨x, hxJ, hxI, hxi⟩ := augmentation_of_axiom2' h1 h2' J hJ.2.1 _ I rfl hI.2.1 hlt
    have := hI.2.2 (insert x I) (Finset.subset_insert x I)
      (Finset.insert_subset (hJ.1 hxJ) hI.1) hxi
    exact hxI (this ▸ Finset.mem_insert_self x I)
  · obtain ⟨x, hxI, hxJ, hxi⟩ := augmentation_of_axiom2' h1 h2' I hI.2.1 _ J rfl hJ.2.1 hlt
    have := hJ.2.2 (insert x J) (Finset.subset_insert x J)
      (Finset.insert_subset (hI.1 hxI) hJ.1) hxi
    exact hxJ (this ▸ Finset.mem_insert_self x J)


theorem proposition_1 {α : Type*} [Fintype α] [DecidableEq α] (Indep : Finset α → Prop) :
    (IndepI1 Indep ∧ Axiom2 Indep) ↔ (IndepI1 Indep ∧ Axiom2' Indep) :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1, axiom2'_of_axiom2 h1 h2⟩,
    fun ⟨h1, h2'⟩ => ⟨h1, axiom2_of_axiom2' h1 h2'⟩⟩

theorem proposition_2 {α : Type*} [Fintype α] [DecidableEq α] :
    (∀ Indep : Finset α → Prop, IndepI1 Indep → Axiom2' Indep →
      Axiom1c (IsCircuit Indep) ∧ Axiom2c (IsCircuit Indep) ∧
        indepOfCircuits (IsCircuit Indep) = Indep) ∧
    (∀ Circ : Finset α → Prop, Axiom1c Circ → Axiom2c Circ →
      IndepI1 (indepOfCircuits Circ) ∧ Axiom2' (indepOfCircuits Circ) ∧
        IsCircuit (indepOfCircuits Circ) = Circ) := by
  refine ⟨fun Indep h1 h2' => ⟨axiom1c_isCircuit, axiom2c_of_axiom2' h2', ?_⟩, ?_⟩
  · funext I
    apply propext
    constructor
    · intro hI
      by_contra hd
      obtain ⟨C, hCs, hC⟩ := exists_circuit_subset hd
      exact hI C hC hCs
    · intro hI C hC hCs
      exact hC.1 (h1 _ _ hCs hI)
  · intro Circ h1c h2c
    have hcirc : IsCircuit (indepOfCircuits Circ) = Circ := by
      funext C
      apply propext
      constructor
      · rintro ⟨hnd, hmin⟩
        have : ∃ C', Circ C' ∧ C' ⊆ C := by
          by_contra hno
          push Not at hno
          exact hnd (fun C' hC' hs => hno C' hC' hs)
        obtain ⟨C', hC', hs⟩ := this
        by_cases hCC : C' = C
        · exact hCC ▸ hC'
        · exact (hmin C' (Finset.ssubset_iff_subset_ne.2 ⟨hs, hCC⟩) C' hC'
            (Finset.Subset.refl _)).elim
      · intro hC
        refine ⟨fun h => h C hC (Finset.Subset.refl _), fun D hD C' hC' hs => ?_⟩
        have hss : C' ⊆ C := hs.trans hD.subset
        have := h1c C' C hC' hC hss
        subst this
        exact (Finset.ssubset_def.1 hD).2 hs
    refine ⟨?_, ?_, hcirc⟩
    · intro N N' hNN' hN' C hC hs
      exact hN' C hC (hs.trans hNN')
    · intro I e hI C1 C2 hC1 hC2 hs1 hs2
      rw [hcirc] at hC1 hC2
      by_contra hne
      have he : ∀ C, Circ C → C ⊆ insert e I → e ∈ C := by
        intro C hC hCs
        by_contra hn
        refine hI C hC ?_
        intro x hx
        rcases Finset.mem_insert.1 (hCs hx) with rfl | h
        · exact absurd hx hn
        · exact h
      obtain ⟨C, hC, hCs⟩ := h2c C1 C2 e hC1 hC2 hne (he C1 hC1 hs1) (he C2 hC2 hs2)
      refine hI C hC ?_
      intro x hx
      obtain ⟨hxe, hx'⟩ := Finset.mem_erase.1 (hCs hx)
      rcases Finset.mem_union.1 hx' with h | h
      · rcases Finset.mem_insert.1 (hs1 h) with h' | h'
        · exact absurd h' hxe
        · exact h'
      · rcases Finset.mem_insert.1 (hs2 h) with h' | h'
        · exact absurd h' hxe
        · exact h'

end EdmondsWork

namespace EdmondsWork

open WhitneyMatroid.RankIndep EdmondsPartition.Main

/-- Strong circuit elimination in a matroid, via the closure operator. -/
theorem strong_elimination {α : Type*} [Fintype α] [DecidableEq α] {Indep : Finset α → Prop}
    (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) {C1 C2 : Finset α} {e a : α}
    (hC1 : IsCircuit Indep C1) (hC2 : IsCircuit Indep C2) (he1 : e ∈ C1) (he2 : e ∈ C2)
    (ha1 : a ∈ C1) (ha2 : a ∉ C2) :
    ∃ C, IsCircuit Indep C ∧ a ∈ C ∧ C ⊆ (C1 ∪ C2).erase e := by
  have hae : a ≠ e := fun h => ha2 (h ▸ he2)
  set X := (C1 ∪ C2).erase e with hX
  set Z := X.erase a with hZ
  have hZX : Z ⊆ X := Finset.erase_subset a X
  have hC2Z : C2.erase e ⊆ Z := by
    intro x hx
    obtain ⟨hxe, hxC⟩ := Finset.mem_erase.1 hx
    exact Finset.mem_erase.2 ⟨fun h => ha2 (h ▸ hxC),
      Finset.mem_erase.2 ⟨hxe, Finset.mem_union_right _ hxC⟩⟩
  have heZ : e ∈ clos Indep Z := by
    have h := circuit_closes h1 h2 h0 hC2 he2 ∅
    rw [Finset.empty_union] at h
    exact clos_subset_of_subset_clos h1 h2 h0 (hC2Z.trans (subset_clos Z)) h
  have haZ : a ∈ clos Indep Z := by
    have h := circuit_closes h1 h2 h0 hC1 ha1 ∅
    rw [Finset.empty_union] at h
    refine clos_subset_of_subset_clos h1 h2 h0 (B := C1.erase a) ?_ h
    intro x hx
    obtain ⟨hxa, hxC⟩ := Finset.mem_erase.1 hx
    by_cases hxe : x = e
    · exact hxe ▸ heZ
    · exact subset_clos Z (Finset.mem_erase.2 ⟨hxa, Finset.mem_erase.2
        ⟨hxe, Finset.mem_union_left _ hxC⟩⟩)
  have haZ' : a ∉ Z := Finset.notMem_erase a X
  obtain ⟨C, hC, haC, hCs⟩ := exists_circuit_of_mem_clos h1 h0 haZ haZ'
  refine ⟨C, hC, haC, fun x hx => ?_⟩
  rcases Finset.mem_insert.1 (hCs hx) with rfl | h
  · exact Finset.mem_erase.2 ⟨hae, Finset.mem_union_left _ ha1⟩
  · exact hZX h

theorem proposition_3 {α : Type*} [Fintype α] [DecidableEq α]
    (Circ : Finset α → Prop) (h1c : Axiom1c Circ) (h2c : Axiom2c Circ) :
    ∀ (C₁ C₂ : Finset α) (e a : α), Circ C₁ → Circ C₂ → e ∈ C₁ → e ∈ C₂ → a ∈ C₁ → a ∉ C₂ →
      ∃ C : Finset α, Circ C ∧ a ∈ C ∧ C ⊆ (C₁ ∪ C₂).erase e := by
  intro C₁ C₂ e a hC1 hC2 he1 he2 ha1 ha2
  obtain ⟨hI1, hI2', hcirc⟩ := (proposition_2 (α := α)).2 Circ h1c h2c
  have h2 : Axiom2 (indepOfCircuits Circ) := axiom2_of_axiom2' hI1 hI2'
  have h0 : indepOfCircuits Circ ∅ := by
    intro C hC hsub
    have hCe : C = ∅ := Finset.subset_empty.1 hsub
    subst hCe
    have := h1c ∅ C₁ hC hC1 (Finset.empty_subset _)
    exact (Finset.notMem_empty e) (this ▸ he1)
  rw [← hcirc] at hC1 hC2 ⊢
  exact strong_elimination hI1 h2 h0 hC1 hC2 he1 he2 ha1 ha2

end EdmondsWork

open WhitneyMatroid.RankIndep EdmondsPartition.Main

theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (Circ : Finset α → Prop) (h1c : Axiom1c Circ) (h2c : Axiom2c Circ) :
    ∀ (C₁ C₂ : Finset α) (e a : α), Circ C₁ → Circ C₂ → e ∈ C₁ → e ∈ C₂ → a ∈ C₁ → a ∉ C₂ →
      ∃ C : Finset α, Circ C ∧ a ∈ C ∧ C ⊆ (C₁ ∪ C₂).erase e :=
  EdmondsWork.proposition_3 Circ h1c h2c

#print axioms solution

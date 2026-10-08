-- Prove2me | solution 1 for EdmondsPartition.Main.span_facts
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T15:28:25.484428+00:00
-- url     : https://prove2.me/submissions/6c2a9190-a1a4-4ece-b011-567649246b24

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

open WhitneyMatroid.RankIndep EdmondsPartition.Main

theorem solution {α : Type*} [Fintype α] [DecidableEq α] (Indep : Finset α → Prop)
    (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) (J : Finset α) :
    (∀ e : α, e ∈ spanOf Indep J ↔ rankOfIndep Indep (insert e J) = rankOfIndep Indep J) ∧
      IsSpan Indep (spanOf Indep J) ∧
      rankOfIndep Indep (spanOf Indep J) = rankOfIndep Indep J :=
  EdmondsWork.span_facts h1 h2 h0 J

#print axioms solution

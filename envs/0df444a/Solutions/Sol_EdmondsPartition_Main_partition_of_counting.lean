-- Prove2me | solution 1 for EdmondsPartition.Main.partition_of_counting
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T15:28:23.984441+00:00
-- url     : https://prove2.me/submissions/f190a6b1-c627-4e48-a46a-8521637bff37

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic
import Theorems.Thm_EdmondsPartition_Main_rado_rank

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

variable {ι β : Type*} [DecidableEq ι] [DecidableEq β]

/-- Hall's condition for the family `A` with respect to the rank function `r`. -/
def RHall (r : Finset β → ℤ) (A : ι → Finset β) : Prop :=
  ∀ J : Finset ι, (J.card : ℤ) ≤ r (J.biUnion A)

theorem rado_rank [Fintype ι] (r : Finset β → ℤ)
    (hmono : ∀ {X Y : Finset β}, X ⊆ Y → r X ≤ r Y)
    (hsub : ∀ X Y : Finset β, r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y)
    (hcard : ∀ X : Finset β, r X ≤ X.card)
    (A : ι → Finset β) (hA : RHall r A) :
    ∃ a : ι → β, (∀ i, a i ∈ A i) ∧ r (Finset.univ.image a) = Fintype.card ι :=
  EdmondsPartition.Main.rado_rank r hmono hsub hcard A hA

end EdmondsWork

namespace EdmondsWork

open WhitneyMatroid.RankIndep EdmondsPartition.Main

variable {α : Type*} [DecidableEq α] {Indep : Finset α → Prop}

/-- The rank of the `k`-fold direct sum of the matroid, on `α × Fin k`. -/
noncomputable def sumRank (Indep : Finset α → Prop) (k : ℕ) (T : Finset (α × Fin k)) : ℤ :=
  ∑ i : Fin k, rankOfIndep Indep ((T.filter (fun p => p.2 = i)).image Prod.fst)

theorem sumRank_mono (h0 : Indep ∅) (k : ℕ) {T T' : Finset (α × Fin k)} (h : T ⊆ T') :
    sumRank Indep k T ≤ sumRank Indep k T' := by
  unfold sumRank
  refine Finset.sum_le_sum fun i _ => rank_mono h0 ?_
  exact Finset.image_subset_image (Finset.filter_subset_filter _ h)

theorem sumRank_submod (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) (k : ℕ)
    (T T' : Finset (α × Fin k)) :
    sumRank Indep k (T ∪ T') + sumRank Indep k (T ∩ T') ≤
      sumRank Indep k T + sumRank Indep k T' := by
  unfold sumRank
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hu : ((T ∪ T').filter (fun p => p.2 = i)).image Prod.fst =
      (T.filter (fun p => p.2 = i)).image Prod.fst ∪ (T'.filter (fun p => p.2 = i)).image Prod.fst := by
    rw [Finset.filter_union, Finset.image_union]
  have hi : ((T ∩ T').filter (fun p => p.2 = i)).image Prod.fst ⊆
      (T.filter (fun p => p.2 = i)).image Prod.fst ∩ (T'.filter (fun p => p.2 = i)).image Prod.fst := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    simp only [Finset.mem_filter, Finset.mem_inter] at hp
    exact Finset.mem_inter.2 ⟨Finset.mem_image.2 ⟨p, Finset.mem_filter.2 ⟨hp.1.1, hp.2⟩, rfl⟩,
      Finset.mem_image.2 ⟨p, Finset.mem_filter.2 ⟨hp.1.2, hp.2⟩, rfl⟩⟩
  have := rank_submod h1 h2 h0 ((T.filter (fun p => p.2 = i)).image Prod.fst)
    ((T'.filter (fun p => p.2 = i)).image Prod.fst)
  have hm := rank_mono h0 hi
  rw [hu]
  linarith

theorem sumRank_le_card (h0 : Indep ∅) (k : ℕ) (T : Finset (α × Fin k)) :
    sumRank Indep k T ≤ T.card := by
  unfold sumRank
  have hc : (T.card : ℤ) = ∑ i : Fin k, ((T.filter (fun p => p.2 = i)).card : ℤ) := by
    have := Finset.card_eq_sum_card_fiberwise (s := T) (t := (Finset.univ : Finset (Fin k)))
      (f := Prod.snd) (fun x _ => Finset.mem_univ _)
    exact_mod_cast this
  rw [hc]
  refine Finset.sum_le_sum fun i _ => ?_
  exact (rank_le_card h0 _).trans (by exact_mod_cast Finset.card_image_le)

/-- Edmonds' partition theorem in counting form: if `|J| ≤ k r(J)` for every `J ⊆ U`, then `U` is
a union of `k` mutually disjoint independent sets. -/
theorem partition_of_counting [Fintype α] (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅)
    (k : ℕ) (U : Finset α)
    (hU : ∀ J : Finset α, J ⊆ U → (J.card : ℤ) ≤ (k : ℤ) * rankOfIndep Indep J) :
    ∃ I : Fin k → Finset α, (∀ i, Indep (I i)) ∧
      (Set.univ : Set (Fin k)).PairwiseDisjoint I ∧ Finset.univ.biUnion I = U := by
  classical
  let A : U → Finset (α × Fin k) := fun e => Finset.univ.image (fun i : Fin k => (e.1, i))
  have hHall : RHall (sumRank Indep k) A := by
    intro J
    have hfib : ∀ i : Fin k,
        ((J.biUnion A).filter (fun p => p.2 = i)).image Prod.fst = J.image Subtype.val := by
      intro i
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and,
        A]
      constructor
      · rintro ⟨p, ⟨⟨e, he, j, rfl⟩, hj⟩, rfl⟩
        exact ⟨e, he, rfl⟩
      · rintro ⟨e, he, rfl⟩
        exact ⟨(e.1, i), ⟨⟨e, he, i, rfl⟩, rfl⟩, rfl⟩
    unfold sumRank
    simp only [hfib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have := hU (J.image Subtype.val) (by
      intro x hx
      obtain ⟨e, _, rfl⟩ := Finset.mem_image.1 hx
      exact e.2)
    rwa [Finset.card_image_of_injective _ Subtype.val_injective] at this
  obtain ⟨a, haA, hrk⟩ := rado_rank (sumRank Indep k) (fun h => sumRank_mono h0 k h)
    (sumRank_submod h1 h2 h0 k) (sumRank_le_card h0 k) A hHall
  have hfst : ∀ e : U, (a e).1 = e.1 := by
    intro e
    obtain ⟨j, _, hj⟩ := Finset.mem_image.1 (haA e)
    rw [← hj]
  let X : Fin k → Finset α := fun i => ((Finset.univ.image a).filter (fun p => p.2 = i)).image Prod.fst
  have hmem : ∀ i x, x ∈ X i ↔ ∃ e : U, (a e).2 = i ∧ e.1 = x := by
    intro i x
    simp only [X, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, ⟨⟨e, rfl⟩, hi⟩, rfl⟩
      exact ⟨e, hi, (hfst e).symm⟩
    · rintro ⟨e, hi, rfl⟩
      exact ⟨a e, ⟨⟨e, rfl⟩, hi⟩, hfst e⟩
  -- each part is independent
  have hcardU : (Fintype.card U : ℤ) = (U.card : ℤ) := by simp
  have hsumX : ∑ i, ((X i).card : ℤ) ≤ (U.card : ℤ) := by
    have hc : ((Finset.univ.image a).card : ℤ) =
        ∑ i : Fin k, (((Finset.univ.image a).filter (fun p => p.2 = i)).card : ℤ) := by
      have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.image a)
        (t := (Finset.univ : Finset (Fin k))) (f := Prod.snd) (fun x _ => Finset.mem_univ _)
      exact_mod_cast this
    have himg : ((Finset.univ.image a).card : ℤ) ≤ (U.card : ℤ) := by
      rw [← hcardU]
      exact_mod_cast (Finset.card_image_le.trans (by simp))
    have hX : ∑ i, ((X i).card : ℤ) ≤
        ∑ i : Fin k, (((Finset.univ.image a).filter (fun p => p.2 = i)).card : ℤ) :=
      Finset.sum_le_sum fun i _ => by exact_mod_cast Finset.card_image_le
    linarith
  have hrk' : ∑ i, rankOfIndep Indep (X i) = (U.card : ℤ) := by
    have : sumRank Indep k (Finset.univ.image a) = ∑ i, rankOfIndep Indep (X i) := rfl
    rw [← this, hrk, hcardU]
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin k)), rankOfIndep Indep (X i) = ((X i).card : ℤ) := by
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin k)), rankOfIndep Indep (X i) ≤ ((X i).card : ℤ) :=
      fun i _ => rank_le_card h0 _
    exact (Finset.sum_eq_sum_iff_of_le hle).1
      (le_antisymm (Finset.sum_le_sum hle) (by rw [hrk']; exact hsumX))
  refine ⟨X, fun i => indep_of_rank_eq_card h0 (hterm i (Finset.mem_univ _)), ?_, ?_⟩
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    obtain ⟨e, he, hex⟩ := (hmem i x).1 hxi
    obtain ⟨e', he', hex'⟩ := (hmem j x).1 hxj
    have : e = e' := Subtype.ext (hex.trans hex'.symm)
    subst this
    exact hij (he.symm.trans he')
  · ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨e, _, rfl⟩ := (hmem i x).1 hi
      exact e.2
    · intro hx
      exact ⟨(a ⟨x, hx⟩).2, (hmem _ x).2 ⟨⟨x, hx⟩, rfl, rfl⟩⟩

end EdmondsWork

open WhitneyMatroid.RankIndep EdmondsPartition.Main

theorem solution {α : Type*} [Fintype α] [DecidableEq α] (Indep : Finset α → Prop)
    (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) (k : ℕ) (U : Finset α)
    (hU : ∀ J : Finset α, J ⊆ U → (J.card : ℤ) ≤ (k : ℤ) * rankOfIndep Indep J) :
    ∃ I : Fin k → Finset α, (∀ i, Indep (I i)) ∧
      (Set.univ : Set (Fin k)).PairwiseDisjoint I ∧ Finset.univ.biUnion I = U :=
  EdmondsWork.partition_of_counting (Indep := Indep) h1 h2 h0 k U hU

#print axioms solution

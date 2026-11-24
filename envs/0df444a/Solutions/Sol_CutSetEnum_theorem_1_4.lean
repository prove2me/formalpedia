-- Prove2me | solution 1 for CutSetEnum.theorem_1_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T08:12:38.521004+00:00
-- url     : https://prove2.me/submissions/c0f302ef-a8da-4fe2-be03-5f0ae6f4c3f7

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Definitions.Def_CutSetEnum_cutSet
import Definitions.Def_CutSetEnum_IsOptKCutValue
import Theorems.Thm_HyperKCut_Structure_cut_sym_submod
import Theorems.Thm_HyperKCut_Structure_source_max_cut
import Theorems.Thm_CutSetEnum_theorem_2_1
import Theorems.Thm_CutSetEnum_corollary_3_1

namespace CutSetEnumTheorem14Proof

open HyperKCut.Structure CutSetEnum

private lemma meets_mono {V : Type} [Fintype V] [DecidableEq V]
    {e X Y : Finset V} (hXY : X ⊆ Y) (h : Meets e X) : Meets e Y := by
  rcases h with ⟨v, hv⟩
  exact ⟨v, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, hXY (Finset.mem_inter.mp hv).2⟩⟩

private lemma filter_card_le_of_imp {α : Type*} (s : Multiset α) (p r : α → Prop)
    [DecidablePred p] [DecidablePred r] :
    (∀ a ∈ s, p a → r a) → (s.filter p).card ≤ (s.filter r).card := by
  refine Multiset.induction_on s (by simp) fun a t ih himp => ?_
  have iht := ih fun x hx => himp x (Multiset.mem_cons_of_mem hx)
  have ha := himp a (Multiset.mem_cons_self a t)
  by_cases hp : p a
  · have hr : r a := ha hp
    rw [Multiset.filter_cons_of_pos _ hp, Multiset.filter_cons_of_pos _ hr,
      Multiset.card_cons, Multiset.card_cons]
    omega
  · by_cases hr : r a
    · rw [Multiset.filter_cons_of_neg _ hp, Multiset.filter_cons_of_pos _ hr,
        Multiset.card_cons]
      omega
    · rw [Multiset.filter_cons_of_neg _ hp, Multiset.filter_cons_of_neg _ hr]
      exact iht

private lemma filter_eq_of_imp_of_card_le {α : Type*} (s : Multiset α) (p r : α → Prop)
    [DecidablePred p] [DecidablePred r] :
    (∀ a ∈ s, p a → r a) → (s.filter r).card ≤ (s.filter p).card →
      s.filter r = s.filter p := by
  refine Multiset.induction_on s (by simp) fun a t ih himp hcard => ?_
  have ht_imp : ∀ x ∈ t, p x → r x := fun x hx => himp x (Multiset.mem_cons_of_mem hx)
  have ht_le : (t.filter p).card ≤ (t.filter r).card := filter_card_le_of_imp t p r ht_imp
  have ha := himp a (Multiset.mem_cons_self a t)
  by_cases hp : p a
  · have hr : r a := ha hp
    rw [Multiset.filter_cons_of_pos _ hp, Multiset.filter_cons_of_pos _ hr,
      Multiset.card_cons, Multiset.card_cons] at hcard
    rw [Multiset.filter_cons_of_pos _ hp, Multiset.filter_cons_of_pos _ hr,
      ih ht_imp (by omega)]
  · by_cases hr : r a
    · rw [Multiset.filter_cons_of_neg _ hp, Multiset.filter_cons_of_pos _ hr,
        Multiset.card_cons] at hcard
      omega
    · rw [Multiset.filter_cons_of_neg _ hp, Multiset.filter_cons_of_neg _ hr] at hcard ⊢
      exact ih ht_imp hcard

theorem theorem_1_4_proof
    {V : Type} [Fintype V] [DecidableEq V]
    (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty)
    (hopt : IsOptKCutValue H k (d H U)) :
    ∃ S T : Finset V, S ⊆ U ∧ T ⊆ Uᶜ ∧ S.Nonempty ∧ T.Nonempty ∧
      S.card ≤ 2 * k - 1 ∧ T.card ≤ 2 * k - 1 ∧
      ∀ A : Finset V, IsMinTerminalCut H S T A → cutSet H A = cutSet H U := by
  obtain ⟨S, hSU, hSne, hScard, hSrec⟩ := CutSetEnum.theorem_2_1 H k hk U hU hUc hopt
  obtain ⟨T, hTU, hTne, hTcard, hTrec⟩ := CutSetEnum.corollary_3_1 H k hk U hU hUc hopt
  have hSUc : Disjoint S Uᶜ :=
    Finset.disjoint_left.mpr fun x hxS hxUc => Finset.mem_compl.mp hxUc (hSU hxS)
  obtain ⟨B, ⟨hBmin, _⟩, _⟩ := (HyperKCut.Structure.source_max_cut H S Uᶜ hSUc).2
  have hBd : d H B = d H U := congrArg Multiset.card (hSrec B hBmin)
  have hS_lb : ∀ X : Finset V, IsTerminalCut S Uᶜ X → d H U ≤ d H X :=
    fun X hX => hBd ▸ hBmin.2 X hX
  have hUT : Disjoint U T :=
    Finset.disjoint_left.mpr fun x hxU hxT => Finset.mem_compl.mp (hTU hxT) hxU
  obtain ⟨C, ⟨hCmin, _⟩, _⟩ := (HyperKCut.Structure.source_max_cut H U T hUT).2
  have hCd : d H C = d H U := congrArg Multiset.card (hTrec C hCmin)
  have hT_lb : ∀ X : Finset V, IsTerminalCut U T X → d H U ≤ d H X :=
    fun X hX => hCd ▸ hCmin.2 X hX
  refine ⟨S, T, hSU, hTU, hSne, hTne, hScard, hTcard, fun A hA => ?_⟩
  have hUTerm : IsTerminalCut S T U := ⟨hSU, hUT⟩
  have hdAU : d H A ≤ d H U := hA.2 U hUTerm
  have hInterTerm : IsTerminalCut S Uᶜ (A ∩ U) :=
    ⟨Finset.subset_inter hA.1.1 hSU,
      Finset.disjoint_left.mpr fun x hx hxUc =>
        Finset.mem_compl.mp hxUc (Finset.mem_inter.mp hx).2⟩
  have hUnionTerm : IsTerminalCut U T (A ∪ U) :=
    ⟨Finset.subset_union_right, Finset.disjoint_union_left.mpr ⟨hA.1.2, hUT⟩⟩
  have hdInter : d H U ≤ d H (A ∩ U) := hS_lb (A ∩ U) hInterTerm
  have hdUnion : d H U ≤ d H (A ∪ U) := hT_lb (A ∪ U) hUnionTerm
  have hsub : d H (A ∪ U) + d H (A ∩ U) ≤ d H A + d H U := by
    have hsubR := (HyperKCut.Structure.cut_sym_submod H).2 A U
    dsimp only at hsubR
    exact_mod_cast hsubR
  have hdInter_eq : d H (A ∩ U) = d H U := by omega
  have hdUnion_eq : d H (A ∪ U) = d H U := by omega
  have hInterMin : IsMinTerminalCut H S Uᶜ (A ∩ U) :=
    ⟨hInterTerm, fun X hX => hdInter_eq ▸ hS_lb X hX⟩
  have hUnionMin : IsMinTerminalCut H U T (A ∪ U) :=
    ⟨hUnionTerm, fun X hX => hdUnion_eq ▸ hT_lb X hX⟩
  have hInterCut : cutSet H (A ∩ U) = cutSet H U := hSrec (A ∩ U) hInterMin
  have hUnionCut : cutSet H (A ∪ U) = cutSet H U := hTrec (A ∪ U) hUnionMin
  have hComplSub : (A ∪ U)ᶜ ⊆ Aᶜ := fun v hv =>
    Finset.mem_compl.mpr fun hvA => Finset.mem_compl.mp hv (Finset.mem_union_left U hvA)
  apply filter_eq_of_imp_of_card_le H.edges
    (fun e => Meets e U ∧ Meets e Uᶜ)
    (fun e => Meets e A ∧ Meets e Aᶜ)
  · intro e he hp
    have heU : e ∈ cutSet H U := Multiset.mem_filter.mpr ⟨he, hp⟩
    have heInterMem : e ∈ H.edges.filter (fun e => Meets e (A ∩ U) ∧ Meets e (A ∩ U)ᶜ) := by
      change e ∈ cutSet H (A ∩ U)
      rwa [hInterCut]
    have heUnionMem : e ∈ H.edges.filter (fun e => Meets e (A ∪ U) ∧ Meets e (A ∪ U)ᶜ) := by
      change e ∈ cutSet H (A ∪ U)
      rwa [hUnionCut]
    have heInter := (Multiset.mem_filter.mp heInterMem).2
    have heUnion := (Multiset.mem_filter.mp heUnionMem).2
    exact ⟨meets_mono Finset.inter_subset_left heInter.1, meets_mono hComplSub heUnion.2⟩
  · exact hdAU

end CutSetEnumTheorem14Proof

open HyperKCut.Structure CutSetEnum

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty)
    (hopt : IsOptKCutValue H k (d H U)) :
    ∃ S T : Finset V, S ⊆ U ∧ T ⊆ Uᶜ ∧ S.Nonempty ∧ T.Nonempty ∧
      S.card ≤ 2 * k - 1 ∧ T.card ≤ 2 * k - 1 ∧
      ∀ A : Finset V, IsMinTerminalCut H S T A → cutSet H A = cutSet H U :=
  CutSetEnumTheorem14Proof.theorem_1_4_proof H k hk U hU hUc hopt

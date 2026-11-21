-- Prove2me | solution 1 for CutSetEnum.claim_2_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:17:07.762616+00:00
-- url     : https://prove2.me/submissions/faeb1ae9-b764-4864-b074-643971a8d94a

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Definitions.Def_CutSetEnum_cutSet
import Definitions.Def_CutSetEnum_IsOptKCutValue
import Definitions.Def_CutSetEnum_IsSourceMinMinTerminalCut
import Definitions.Def_CutSetEnum_Coll
import Definitions.Def_CutSetEnum_IsMinTransversal
set_option autoImplicit false

namespace Aux_CutSetEnum_claim_2_3

open HyperKCut.Structure CutSetEnum

variable {V : Type} [Fintype V] [DecidableEq V]

theorem cutSet_compl (H : HyperKCut.Structure.Hypergraph V) (A : Finset V) :
    cutSet H Aᶜ = cutSet H A := by
  unfold cutSet
  apply Multiset.filter_congr
  intro e _
  rw [compl_compl]
  exact and_comm

theorem d_eq_card (H : HyperKCut.Structure.Hypergraph V) (A : Finset V) :
    d H A = (cutSet H A).card := rfl

theorem d_compl (H : HyperKCut.Structure.Hypergraph V) (A : Finset V) :
    d H Aᶜ = d H A := by
  rw [d_eq_card, d_eq_card, cutSet_compl]

/-- the core of Proposition 2.1: any minimum `(S, Uᶜ)`-terminal cut of a transversal -/
theorem min_cut_of_transversal (H : HyperKCut.Structure.Hypergraph V) (U S : Finset V)
    (hSU : S ⊆ U) (hT : IsTransversal H U S) (A : Finset V)
    (hA : IsMinTerminalCut H S Uᶜ A) : cutSet H A = cutSet H U := by
  by_contra hne
  obtain ⟨⟨hSA, hAd⟩, hmin⟩ := hA
  have hdU : d H A ≤ d H U := hmin U ⟨hSU, disjoint_compl_right⟩
  have hAU : A ⊆ U := by
    intro x hx
    by_contra hxU
    exact Finset.disjoint_left.mp hAd hx (Finset.mem_compl.mpr hxU)
  have hmem : Aᶜ ∈ Coll H U := by
    show Uᶜ ⊂ Aᶜ ∧ d H Aᶜ ≤ d H U ∧ cutSet H Aᶜ ≠ cutSet H U
    refine ⟨?_, ?_, ?_⟩
    · refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.compl_subset_compl.mpr hAU, ?_⟩
      intro heq
      have : A = U := compl_injective heq.symm
      apply hne
      rw [this]
    · rw [d_compl]
      exact hdU
    · rw [cutSet_compl]
      exact hne
  obtain ⟨x, hx⟩ := hT _ hmem
  rw [Finset.mem_inter, Finset.mem_compl] at hx
  exact hx.2 (hSA hx.1)
lemma meets_of (e X : Finset V) (x : V) (he : x ∈ e) (hX : x ∈ X) : Meets e X :=
  ⟨x, Finset.mem_inter.mpr ⟨he, hX⟩⟩

lemma meets_elim {e X : Finset V} (h : Meets e X) : ∃ x, x ∈ e ∧ x ∈ X := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, Finset.mem_inter.mp hx⟩

lemma comb (P Q R T : Prop) [Decidable P] [Decidable Q] [Decidable R] [Decidable T]
    (h1 : P → R ∨ T) (h2 : Q → R ∨ T) (h3 : P → Q → R ∧ T) :
    ((if P then 1 else 0) + (if Q then 1 else 0) : ℕ) ≤
      (if R then 1 else 0) + (if T then 1 else 0) := by
  split_ifs <;> first | omega | (exfalso; tauto)

lemma edge_sub (e A B : Finset V) :
    ((if Meets e (A ∩ B) ∧ Meets e (A ∩ B)ᶜ then 1 else 0) +
      (if Meets e (A ∪ B) ∧ Meets e (A ∪ B)ᶜ then 1 else 0) : ℕ) ≤
      (if Meets e A ∧ Meets e Aᶜ then 1 else 0) + (if Meets e B ∧ Meets e Bᶜ then 1 else 0) := by
  apply comb
  · rintro ⟨m1, m2⟩
    obtain ⟨x, hxe, hx⟩ := meets_elim m1
    obtain ⟨y, hye, hy⟩ := meets_elim m2
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_compl, Finset.mem_inter] at hy
    by_cases hyA : y ∈ A
    · right
      exact ⟨meets_of e B x hxe hx.2,
        meets_of e Bᶜ y hye (Finset.mem_compl.mpr (fun hyB => hy ⟨hyA, hyB⟩))⟩
    · left
      exact ⟨meets_of e A x hxe hx.1, meets_of e Aᶜ y hye (Finset.mem_compl.mpr hyA)⟩
  · rintro ⟨m1, m2⟩
    obtain ⟨x, hxe, hx⟩ := meets_elim m1
    obtain ⟨z, hze, hz⟩ := meets_elim m2
    rw [Finset.mem_union] at hx
    rw [Finset.mem_compl, Finset.mem_union] at hz
    rcases hx with hxA | hxB
    · left
      exact ⟨meets_of e A x hxe hxA,
        meets_of e Aᶜ z hze (Finset.mem_compl.mpr (fun h => hz (Or.inl h)))⟩
    · right
      exact ⟨meets_of e B x hxe hxB,
        meets_of e Bᶜ z hze (Finset.mem_compl.mpr (fun h => hz (Or.inr h)))⟩
  · rintro ⟨m1, _⟩ ⟨_, m4⟩
    obtain ⟨x, hxe, hx⟩ := meets_elim m1
    obtain ⟨z, hze, hz⟩ := meets_elim m4
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_compl, Finset.mem_union] at hz
    exact ⟨⟨meets_of e A x hxe hx.1,
        meets_of e Aᶜ z hze (Finset.mem_compl.mpr (fun h => hz (Or.inl h)))⟩,
      ⟨meets_of e B x hxe hx.2,
        meets_of e Bᶜ z hze (Finset.mem_compl.mpr (fun h => hz (Or.inr h)))⟩⟩

lemma submod (H : HyperKCut.Structure.Hypergraph V) (A B : Finset V) :
    d H (A ∩ B) + d H (A ∪ B) ≤ d H A + d H B := by
  unfold d
  rw [← Multiset.countP_eq_card_filter, ← Multiset.countP_eq_card_filter,
    ← Multiset.countP_eq_card_filter, ← Multiset.countP_eq_card_filter]
  generalize H.edges = s
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_cons,
      Multiset.countP_cons]
    have := edge_sub a A B
    omega

lemma mono (H : HyperKCut.Structure.Hypergraph V) (X Y T A B : Finset V) (hXY : X ⊆ Y)
    (hA : IsSourceMinMinTerminalCut H X T A) (hB : IsSourceMinMinTerminalCut H Y T B) :
    A ⊆ B := by
  obtain ⟨⟨⟨hXA, hAT⟩, hAmin⟩, hAsrc⟩ := hA
  obtain ⟨⟨⟨hYB, hBT⟩, hBmin⟩, _⟩ := hB
  have hsub := submod H A B
  have h1 : d H B ≤ d H (A ∪ B) :=
    hBmin (A ∪ B) ⟨hYB.trans Finset.subset_union_right,
      Finset.disjoint_union_left.mpr ⟨hAT, hBT⟩⟩
  have h2 : IsMinTerminalCut H X T (A ∩ B) := by
    refine ⟨⟨Finset.subset_inter hXA (hXY.trans hYB), hAT.mono_left Finset.inter_subset_left⟩, ?_⟩
    intro U' hU'
    have := hAmin U' hU'
    omega
  exact (hAsrc _ h2).trans Finset.inter_subset_right


theorem term_subset_U {H : HyperKCut.Structure.Hypergraph V} {X U A : Finset V}
    (h : IsTerminalCut X Uᶜ A) : A ⊆ U := by
  intro x hx
  by_contra hxU
  exact Finset.disjoint_left.mp h.2 hx (Finset.mem_compl.mpr hxU)

theorem exists_cross_edge (H : HyperKCut.Structure.Hypergraph V) (U Q : Finset V)
    (hd : d H Q = d H U) (hne : cutSet H Q ≠ cutSet H U) :
    ∃ e ∈ H.edges, (Meets e U ∧ Meets e Uᶜ) ∧ ¬ (Meets e Q ∧ Meets e Qᶜ) := by
  by_contra hcon
  push_neg at hcon
  apply hne
  symm
  have h1 : cutSet H U = H.edges.filter
      (fun e => (Meets e U ∧ Meets e Uᶜ) ∧ (Meets e Q ∧ Meets e Qᶜ)) := by
    unfold cutSet
    apply Multiset.filter_congr
    intro e he
    exact ⟨fun h => ⟨h, hcon e he h⟩, fun h => h.1⟩
  have h2 : cutSet H U ≤ cutSet H Q := by
    rw [h1]
    unfold cutSet
    exact Multiset.monotone_filter_right _ (fun b hb => hb.2)
  apply Multiset.eq_of_le_of_card_le h2
  rw [← d_eq_card, ← d_eq_card, hd]

/-- Claim 2.1 core. -/
theorem claim21_core (H : HyperKCut.Structure.Hypergraph V) (U S X : Finset V) (ui : V)
    (hT : IsTransversal H U S) (hX : X = S.erase ui)
    (hmin : ¬ IsTransversal H U X) (Hh : Finset V)
    (hHh : IsSourceMinMinTerminalCut H X Uᶜ Hh) : Hhᶜ ∈ Coll H U := by
  have hnt := hmin
  unfold IsTransversal at hnt
  push_neg at hnt
  obtain ⟨Q, hQ, hQX⟩ := hnt
  obtain ⟨hUQ, hdQ, hcQ⟩ := hQ
  have hXA : X ⊆ Qᶜ := by
    intro x hx
    rw [Finset.mem_compl]
    intro hxQ
    have : x ∈ X ∩ Q := Finset.mem_inter.mpr ⟨hx, hxQ⟩
    rw [hQX] at this
    simp at this
  have hAd : Disjoint Qᶜ Uᶜ := by
    rw [Finset.disjoint_left]
    intro x hx hxU
    exact (Finset.mem_compl.mp hx) (hUQ.1 hxU)
  obtain ⟨⟨⟨hXH, hHd⟩, hHmin⟩, hHsrc⟩ := hHh
  have hHU : Hh ⊆ U := term_subset_U (H := H) ⟨hXH, hHd⟩
  have h1 : d H Hh ≤ d H Qᶜ := hHmin _ ⟨hXA, hAd⟩
  rw [d_compl] at h1
  -- the cut sets differ
  have hcut : cutSet H Hhᶜ ≠ cutSet H U := by
    rw [cutSet_compl]
    by_cases hlt : d H Hh < d H U
    · intro h
      have : d H Hh = d H U := by rw [d_eq_card, d_eq_card, h]
      omega
    · have hdH : d H Hh = d H U := by omega
      have hs := submod H Hh Qᶜ
      have hi : d H Hh ≤ d H (Hh ∩ Qᶜ) := hHmin _
        ⟨Finset.subset_inter hXH hXA, hHd.mono_left Finset.inter_subset_left⟩
      have hu : d H Hh ≤ d H (Hh ∪ Qᶜ) := hHmin _
        ⟨hXH.trans Finset.subset_union_left, Finset.disjoint_union_left.mpr ⟨hHd, hAd⟩⟩
      rw [d_compl] at hs
      have hmin2 : IsMinTerminalCut H X Uᶜ (Hh ∩ Qᶜ) := by
        refine ⟨⟨Finset.subset_inter hXH hXA, hHd.mono_left Finset.inter_subset_left⟩, ?_⟩
        intro U' hU'
        have := hHmin U' hU'
        omega
      have hsubA : Hh ⊆ Qᶜ := (hHsrc _ hmin2).trans Finset.inter_subset_right
      have hdQU : d H Q = d H U := by omega
      obtain ⟨e, he, ⟨heU, heUc⟩, heQ⟩ := exists_cross_edge H U Q hdQU hcQ
      have hmQ : Meets e Q := by
        obtain ⟨x, hx⟩ := heUc
        rw [Finset.mem_inter] at hx
        exact ⟨x, Finset.mem_inter.mpr ⟨hx.1, hUQ.1 hx.2⟩⟩
      have hnQc : ¬ Meets e Qᶜ := fun h => heQ ⟨hmQ, h⟩
      have hnH : ¬ Meets e Hh := by
        intro h
        obtain ⟨x, hx⟩ := h
        rw [Finset.mem_inter] at hx
        exact hnQc ⟨x, Finset.mem_inter.mpr ⟨hx.1, hsubA hx.2⟩⟩
      intro h
      have hmem : e ∈ cutSet H U := by
        unfold cutSet
        rw [Multiset.mem_filter]
        exact ⟨he, heU, heUc⟩
      rw [← h] at hmem
      unfold cutSet at hmem
      rw [Multiset.mem_filter] at hmem
      exact hnH hmem.2.1
  show Uᶜ ⊂ Hhᶜ ∧ d H Hhᶜ ≤ d H U ∧ cutSet H Hhᶜ ≠ cutSet H U
  refine ⟨?_, ?_, hcut⟩
  · refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.compl_subset_compl.mpr hHU, ?_⟩
    intro heq
    have : Hh = U := compl_injective heq.symm
    apply hcut
    rw [this, cutSet_compl]
  · rw [d_compl]
    omega

theorem claim21_full (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (S : Finset V) (hS : IsMinTransversal H U S)
    (p : ℕ) (hp : 2 * k ≤ p) (u : Fin p → V) (hu : Function.Injective u)
    (hSu : S = Finset.univ.image u)
    (Hs : Finset V → Finset V)
    (hHs : ∀ X : Finset V, X ⊆ U → X.Nonempty → IsSourceMinMinTerminalCut H X Uᶜ (Hs X))
    (i : Fin p) : (Hs (S.erase (u i)))ᶜ ∈ Coll H U ∧ u i ∈ (Hs (S.erase (u i)))ᶜ := by
  have hSU : S ⊆ U := hS.1
  have hcard : S.card = p := by
    rw [hSu, Finset.card_image_of_injective _ hu, Finset.card_univ, Fintype.card_fin]
  have hui : u i ∈ S := by rw [hSu]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hY : S.erase (u i) ⊆ U := (Finset.erase_subset _ _).trans hSU
  have hc1 := Finset.pred_card_le_card_erase (s := S) (a := u i)
  have hYne : (S.erase (u i)).Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hmin : ¬ IsTransversal H U (S.erase (u i)) := hS.2.2 _ (Finset.erase_ssubset hui)
  have hHh := hHs _ hY hYne
  have hC := claim21_core H U S (S.erase (u i)) (u i) hS.2.1 rfl hmin _ hHh
  refine ⟨hC, ?_⟩
  obtain ⟨x, hx⟩ := hS.2.1 _ hC
  rw [Finset.mem_inter] at hx
  by_cases hxi : x = u i
  · rw [hxi] at hx
    exact hx.2
  · exfalso
    have hxS : x ∈ S.erase (u i) := Finset.mem_erase.mpr ⟨hxi, hx.1⟩
    exact (Finset.mem_compl.mp hx.2) (hHh.1.1.1 hxS)

theorem meets_iff {e X : Finset V} : Meets e X ↔ ∃ v ∈ e, v ∈ X := by
  unfold Meets
  constructor
  · rintro ⟨v, hv⟩
    rw [Finset.mem_inter] at hv
    exact ⟨v, hv.1, hv.2⟩
  · rintro ⟨v, hv, hx⟩
    exact ⟨v, Finset.mem_inter.mpr ⟨hv, hx⟩⟩

theorem meets_congr {e X Y : Finset V} (h : X = Y) : Meets e X ↔ Meets e Y := by rw [h]

theorem countP_eq_sum {α : Type} (p : α → Prop) [DecidablePred p] (s : Multiset α) :
    s.countP p = (s.map (fun e => if p e then 1 else 0)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.countP_cons, Multiset.map_cons, Multiset.sum_cons, ih]
    ring

theorem d_eq_sum (H : HyperKCut.Structure.Hypergraph V) (X : Finset V) :
    d H X = (H.edges.map (fun e => if Meets e X ∧ Meets e Xᶜ then 1 else 0)).sum := by
  unfold d
  rw [← Multiset.countP_eq_card_filter, countP_eq_sum]

theorem msum_le {α : Type} (s : Multiset α) (f g : α → ℕ) (h : ∀ x ∈ s, f x ≤ g x) :
    (s.map f).sum ≤ (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons]
    have h1 := h a (Multiset.mem_cons_self a s)
    have h2 := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    omega

theorem msum_add {α : Type} (s : Multiset α) (f g : α → ℕ) :
    (s.map (fun x => f x + g x)).sum = (s.map f).sum + (s.map g).sum :=
  Multiset.sum_map_add

theorem msum_finset {α ι : Type} (s : Multiset α) (J : Finset ι) (f : α → ι → ℕ) :
    (s.map (fun x => ∑ i ∈ J, f x i)).sum = ∑ i ∈ J, (s.map (fun x => f x i)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih]
    rw [Finset.sum_add_distrib]

section Parts

variable {p : ℕ} (A : Fin p → Finset V)

def cnt (I : Finset (Fin p)) (v : V) : ℕ := (I.filter (fun i => v ∈ A i)).card
def ZS (I : Finset (Fin p)) : Finset V := Finset.univ.filter (fun v => cnt A I v = 0)
def WS (I : Finset (Fin p)) : Finset V := Finset.univ.filter (fun v => 2 ≤ cnt A I v)
def YS (I : Finset (Fin p)) (i : Fin p) : Finset V := (A i).filter (fun v => cnt A I v = 1)

theorem mem_ZS {I : Finset (Fin p)} {v : V} : v ∈ ZS A I ↔ cnt A I v = 0 := by
  simp [ZS]
theorem mem_WS {I : Finset (Fin p)} {v : V} : v ∈ WS A I ↔ 2 ≤ cnt A I v := by
  simp [WS]
theorem mem_YS {I : Finset (Fin p)} {i : Fin p} {v : V} :
    v ∈ YS A I i ↔ v ∈ A i ∧ cnt A I v = 1 := by
  simp [YS]

theorem cnt_pos {I : Finset (Fin p)} {i : Fin p} {v : V} (hi : i ∈ I) (hv : v ∈ A i) :
    1 ≤ cnt A I v := by
  unfold cnt
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
  intro h
  have : i ∈ I.filter (fun i => v ∈ A i) := Finset.mem_filter.mpr ⟨hi, hv⟩
  rw [h] at this
  simp at this

theorem cnt_one_exists {I : Finset (Fin p)} {v : V} (h : cnt A I v = 1) :
    ∃ i ∈ I, v ∈ A i := by
  unfold cnt at h
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < (I.filter (fun i => v ∈ A i)).card)
  rw [Finset.mem_filter] at hi
  exact ⟨i, hi.1, hi.2⟩

theorem cnt_one_unique {I : Finset (Fin p)} {v : V} (h : cnt A I v = 1) {i j : Fin p}
    (hi : i ∈ I) (hvi : v ∈ A i) (hj : j ∈ I) (hvj : v ∈ A j) : i = j := by
  unfold cnt at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have h1 : i ∈ I.filter (fun i => v ∈ A i) := Finset.mem_filter.mpr ⟨hi, hvi⟩
  have h2 : j ∈ I.filter (fun i => v ∈ A i) := Finset.mem_filter.mpr ⟨hj, hvj⟩
  rw [ha, Finset.mem_singleton] at h1 h2
  rw [h1, h2]

theorem cnt_insert {I : Finset (Fin p)} {q : Fin p} (hq : q ∉ I) (v : V) :
    cnt A (insert q I) v = cnt A I v + (if v ∈ A q then 1 else 0) := by
  unfold cnt
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun h' => hq (Finset.mem_filter.mp h').1)]
  · rw [add_zero]

theorem YS_insert_old {I : Finset (Fin p)} {q : Fin p} (hq : q ∉ I) {i : Fin p} (hi : i ∈ I) :
    YS A (insert q I) i = YS A I i \ A q := by
  ext v
  rw [mem_YS, Finset.mem_sdiff, mem_YS, cnt_insert A hq]
  constructor
  · rintro ⟨h1, h2⟩
    have := cnt_pos A hi h1
    by_cases hvq : v ∈ A q
    · rw [if_pos hvq] at h2; omega
    · rw [if_neg hvq] at h2; exact ⟨⟨h1, by omega⟩, hvq⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rw [if_neg h3]
    exact ⟨h1, by omega⟩

theorem YS_insert_new {I : Finset (Fin p)} {q : Fin p} (hq : q ∉ I) :
    YS A (insert q I) q = ZS A I ∩ A q := by
  ext v
  rw [mem_YS, Finset.mem_inter, mem_ZS, cnt_insert A hq]
  constructor
  · rintro ⟨h1, h2⟩
    rw [if_pos h1] at h2
    exact ⟨by omega, h1⟩
  · rintro ⟨h1, h2⟩
    rw [if_pos h2]
    exact ⟨h2, by omega⟩

theorem ZS_insert {I : Finset (Fin p)} {q : Fin p} (hq : q ∉ I) :
    ZS A (insert q I) = ZS A I \ A q := by
  ext v
  rw [mem_ZS, Finset.mem_sdiff, mem_ZS, cnt_insert A hq]
  by_cases hvq : v ∈ A q
  · simp [hvq]
  · simp [hvq]

theorem WS_insert_mem {I : Finset (Fin p)} {q : Fin p} (hq : q ∉ I) {v : V} :
    v ∈ WS A (insert q I) ↔ v ∈ WS A I ∨ (cnt A I v = 1 ∧ v ∈ A q) := by
  rw [mem_WS, mem_WS, cnt_insert A hq]
  by_cases hvq : v ∈ A q
  · rw [if_pos hvq]
    constructor
    · intro h
      by_cases h2 : 2 ≤ cnt A I v
      · exact Or.inl h2
      · exact Or.inr ⟨by omega, hvq⟩
    · rintro (h | ⟨h, _⟩) <;> omega
  · rw [if_neg hvq]
    constructor
    · intro h; exact Or.inl (by omega)
    · rintro (h | ⟨_, h⟩)
      · omega
      · exact absurd h hvq

/-- per-edge weight -/
def lam (m : ℕ) (w z : Prop) [Decidable w] [Decidable z] : ℕ :=
  if 2 ≤ m + (if w then 1 else 0) + (if z then 1 else 0) then
    (if m = 1 ∧ (w ↔ ¬ z) then 1 else 2) else 0

def mC (I : Finset (Fin p)) (e : Finset V) : ℕ := (I.filter (fun i => Meets e (YS A I i))).card

def lamE (I : Finset (Fin p)) (e : Finset V) : ℕ :=
  lam (mC A I e) (Meets e (WS A I)) (Meets e (ZS A I))

def sig (H : HyperKCut.Structure.Hypergraph V) (I : Finset (Fin p)) : ℕ :=
  (H.edges.map (lamE A I)).sum

end Parts

theorem abs_step (z0 z1 w0 w1 : Prop) [Decidable z0] [Decidable z1] [Decidable w0]
    [Decidable w1] (B C M : ℕ) (h1 : B ≤ M) (h2 : C ≤ M) (h3 : M ≤ B + C) :
    lam (B + (if z1 then 1 else 0)) (w0 ∨ w1 ∨ 0 < C) z0 +
        (if w1 ∧ (z0 ∨ z1 ∨ w0 ∨ 0 < B ∨ 0 < C) then 1 else 0) ≤
      lam M (w0 ∨ w1) (z0 ∨ z1) + (if (z1 ∨ w1 ∨ 0 < C) ∧ (z0 ∨ w0 ∨ 0 < B) then 1 else 0) := by
  unfold lam
  by_cases a : z0 <;> by_cases b : z1 <;> by_cases c : w0 <;> by_cases d : w1 <;>
    simp only [a, b, c, d, true_or, or_true, false_or, or_false, true_and, and_true,
      false_and, and_false, not_true_eq_false, not_false_eq_true, iff_true, iff_false,
      true_iff, false_iff, if_true, if_false, ite_true, ite_false] <;>
    (try split_ifs) <;> omega

theorem lam_congr {m m' : ℕ} {w w' z z' : Prop} [Decidable w] [Decidable w'] [Decidable z]
    [Decidable z'] (hm : m = m') (hw : w ↔ w') (hz : z ↔ z') : lam m w z = lam m' w' z' := by
  unfold lam
  subst hm
  by_cases a : w' <;> by_cases b : z' <;> simp [hw, hz, a, b]

theorem ind_congr {P P' : Prop} [Decidable P] [Decidable P'] (h : P ↔ P') :
    (if P then 1 else 0 : ℕ) = if P' then 1 else 0 := by
  by_cases a : P'
  · rw [if_pos (h.mpr a), if_pos a]
  · rw [if_neg (fun h' => a (h.mp h')), if_neg a]

theorem meets_split (e X Q : Finset V) : Meets e X ↔ Meets e (X \ Q) ∨ Meets e (X ∩ Q) := by
  simp only [meets_iff, Finset.mem_sdiff, Finset.mem_inter]
  constructor
  · rintro ⟨v, hv, hx⟩
    by_cases hq : v ∈ Q
    · exact Or.inr ⟨v, hv, hx, hq⟩
    · exact Or.inl ⟨v, hv, hx, hq⟩
  · rintro (⟨v, hv, hx, _⟩ | ⟨v, hv, hx, _⟩) <;> exact ⟨v, hv, hx⟩

theorem card_filter_pos {ι : Type} (I : Finset ι) (P : ι → Prop) [DecidablePred P] :
    0 < (I.filter P).card ↔ ∃ i ∈ I, P i := by
  rw [Finset.card_pos]
  constructor
  · rintro ⟨i, hi⟩
    rw [Finset.mem_filter] at hi
    exact ⟨i, hi.1, hi.2⟩
  · rintro ⟨i, hi, hp⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hp⟩⟩

section Step

variable {p : ℕ} (A : Fin p → Finset V)

theorem step_edge {I : Finset (Fin p)} {q : Fin p} (hq : q ∉ I) (e : Finset V) :
    lamE A (insert q I) e +
        (if Meets e (WS A I ∩ A q) ∧ Meets e (WS A I ∩ A q)ᶜ then 1 else 0) ≤
      lamE A I e + (if Meets e (A q) ∧ Meets e (A q)ᶜ then 1 else 0) := by
  -- the flags
  obtain ⟨B, hB⟩ : ∃ B, B = (I.filter (fun i => Meets e (YS A I i \ A q))).card := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = (I.filter (fun i => Meets e (YS A I i ∩ A q))).card := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = (I.filter (fun i => Meets e (YS A I i \ A q) ∨ Meets e (YS A I i ∩ A q))).card := ⟨_, rfl⟩
  have hBpos : 0 < B ↔ ∃ i ∈ I, Meets e (YS A I i \ A q) := by rw [hB]; exact card_filter_pos I (fun i => Meets e (YS A I i \ A q))
  have hCpos : 0 < C ↔ ∃ i ∈ I, Meets e (YS A I i ∩ A q) := by rw [hC]; exact card_filter_pos I (fun i => Meets e (YS A I i ∩ A q))
  have h1 : B ≤ M := by
    rw [hB, hM]
    exact Finset.card_le_card (fun i hi => by
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, Or.inl hi.2⟩)
  have h2 : C ≤ M := by
    rw [hC, hM]
    exact Finset.card_le_card (fun i hi => by
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, Or.inr hi.2⟩)
  have h3 : M ≤ B + C := by
    rw [hB, hC, hM, Finset.filter_or]
    exact Finset.card_union_le _ _
  -- old weight
  have eOld : lamE A I e = lam M (Meets e (WS A I \ A q) ∨ Meets e (WS A I ∩ A q)) (Meets e (ZS A I \ A q) ∨ Meets e (ZS A I ∩ A q)) := by
    unfold lamE
    apply lam_congr
    · unfold mC
      rw [hM]
      congr 1
      apply Finset.filter_congr
      intro i _
      exact meets_split e (YS A I i) (A q)
    · exact meets_split e (WS A I) (A q)
    · exact meets_split e (ZS A I) (A q)
  -- new weight
  have eNew : lamE A (insert q I) e = lam (B + (if Meets e (ZS A I ∩ A q) then 1 else 0)) (Meets e (WS A I \ A q) ∨ Meets e (WS A I ∩ A q) ∨ 0 < C) (Meets e (ZS A I \ A q)) := by
    unfold lamE
    apply lam_congr
    · unfold mC
      rw [Finset.filter_insert]
      have hfil : I.filter (fun i => Meets e (YS A (insert q I) i)) = I.filter (fun i => Meets e (YS A I i \ A q)) := by
        apply Finset.filter_congr
        intro i hi
        rw [YS_insert_old A hq hi]
      by_cases hz : Meets e (ZS A I ∩ A q)
      · have : Meets e (YS A (insert q I) q) := by rw [YS_insert_new A hq]; exact hz
        rw [if_pos this, if_pos hz, Finset.card_insert_of_notMem, hfil, hB]
        intro h
        exact hq (Finset.mem_filter.mp h).1
      · have : ¬ Meets e (YS A (insert q I) q) := by rw [YS_insert_new A hq]; exact hz
        rw [if_neg this, if_neg hz, hfil, hB, add_zero]
    · rw [hCpos]
      simp only [meets_iff, Finset.mem_sdiff, Finset.mem_inter]
      constructor
      · rintro ⟨v, hv, hW⟩
        rw [WS_insert_mem A hq] at hW
        rcases hW with hW | ⟨h1', hvq⟩
        · by_cases hvq : v ∈ A q
          · exact Or.inr (Or.inl ⟨v, hv, hW, hvq⟩)
          · exact Or.inl ⟨v, hv, hW, hvq⟩
        · obtain ⟨i, hi, hvi⟩ := cnt_one_exists A h1'
          exact Or.inr (Or.inr ⟨i, hi, v, hv, (mem_YS A).mpr ⟨hvi, h1'⟩, hvq⟩)
      · rintro (⟨v, hv, hW, _⟩ | ⟨v, hv, hW, _⟩ | ⟨i, hi, v, hv, hY, hvq⟩)
        · exact ⟨v, hv, (WS_insert_mem A hq).mpr (Or.inl hW)⟩
        · exact ⟨v, hv, (WS_insert_mem A hq).mpr (Or.inl hW)⟩
        · exact ⟨v, hv, (WS_insert_mem A hq).mpr (Or.inr ⟨((mem_YS A).mp hY).2, hvq⟩)⟩
    · rw [ZS_insert A hq]
  -- the cut indicators
  have eQ : (if Meets e (A q) ∧ Meets e (A q)ᶜ then 1 else 0 : ℕ) =
      if (Meets e (ZS A I ∩ A q) ∨ Meets e (WS A I ∩ A q) ∨ 0 < C) ∧ (Meets e (ZS A I \ A q) ∨ Meets e (WS A I \ A q) ∨ 0 < B) then 1 else 0 := by
    apply ind_congr
    rw [hCpos, hBpos]
    simp only [meets_iff, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_compl]
    constructor
    · rintro ⟨⟨v, hv, hvq⟩, ⟨x, hx, hxq⟩⟩
      refine ⟨?_, ?_⟩
      · rcases Nat.lt_or_ge (cnt A I v) 1 with h | h
        · exact Or.inl ⟨v, hv, (mem_ZS A).mpr (by omega), hvq⟩
        · rcases Nat.lt_or_ge (cnt A I v) 2 with h' | h'
          · obtain ⟨i, hi, hvi⟩ := cnt_one_exists A (by omega : cnt A I v = 1)
            exact Or.inr (Or.inr ⟨i, hi, v, hv, (mem_YS A).mpr ⟨hvi, by omega⟩, hvq⟩)
          · exact Or.inr (Or.inl ⟨v, hv, (mem_WS A).mpr h', hvq⟩)
      · rcases Nat.lt_or_ge (cnt A I x) 1 with h | h
        · exact Or.inl ⟨x, hx, (mem_ZS A).mpr (by omega), hxq⟩
        · rcases Nat.lt_or_ge (cnt A I x) 2 with h' | h'
          · obtain ⟨i, hi, hxi⟩ := cnt_one_exists A (by omega : cnt A I x = 1)
            exact Or.inr (Or.inr ⟨i, hi, x, hx, (mem_YS A).mpr ⟨hxi, by omega⟩, hxq⟩)
          · exact Or.inr (Or.inl ⟨x, hx, (mem_WS A).mpr h', hxq⟩)
    · rintro ⟨h1', h2'⟩
      refine ⟨?_, ?_⟩
      · rcases h1' with ⟨v, hv, _, hvq⟩ | ⟨v, hv, _, hvq⟩ | ⟨i, _, v, hv, _, hvq⟩ <;>
          exact ⟨v, hv, hvq⟩
      · rcases h2' with ⟨v, hv, _, hvq⟩ | ⟨v, hv, _, hvq⟩ | ⟨i, _, v, hv, _, hvq⟩ <;>
          exact ⟨v, hv, hvq⟩
  have eWQ : (if Meets e (WS A I ∩ A q) ∧ Meets e (WS A I ∩ A q)ᶜ then 1 else 0 : ℕ) =
      if Meets e (WS A I ∩ A q) ∧ (Meets e (ZS A I \ A q) ∨ Meets e (ZS A I ∩ A q) ∨ Meets e (WS A I \ A q) ∨ 0 < B ∨ 0 < C) then 1 else 0 := by
    apply ind_congr
    rw [hCpos, hBpos]
    refine and_congr Iff.rfl ?_
    simp only [meets_iff, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_compl]
    constructor
    · rintro ⟨v, hv, hn⟩
      rcases Nat.lt_or_ge (cnt A I v) 1 with h | h
      · by_cases hvq : v ∈ A q
        · exact Or.inr (Or.inl ⟨v, hv, (mem_ZS A).mpr (by omega), hvq⟩)
        · exact Or.inl ⟨v, hv, (mem_ZS A).mpr (by omega), hvq⟩
      · rcases Nat.lt_or_ge (cnt A I v) 2 with h' | h'
        · obtain ⟨i, hi, hvi⟩ := cnt_one_exists A (by omega : cnt A I v = 1)
          have hY : v ∈ YS A I i := (mem_YS A).mpr ⟨hvi, by omega⟩
          by_cases hvq : v ∈ A q
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, v, hv, hY, hvq⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, v, hv, hY, hvq⟩)))
        · have hW : v ∈ WS A I := (mem_WS A).mpr h'
          have hvq : v ∉ A q := fun hvq => hn ⟨hW, hvq⟩
          exact Or.inr (Or.inr (Or.inl ⟨v, hv, hW, hvq⟩))
    · rintro (⟨v, hv, hZ, _⟩ | ⟨v, hv, hZ, _⟩ | ⟨v, hv, _, hvq⟩ | ⟨i, _, v, hv, _, hvq⟩ |
        ⟨i, _, v, hv, hY, _⟩)
      · refine ⟨v, hv, fun h => ?_⟩
        have := (mem_ZS A).mp hZ
        have := (mem_WS A).mp h.1
        omega
      · refine ⟨v, hv, fun h => ?_⟩
        have := (mem_ZS A).mp hZ
        have := (mem_WS A).mp h.1
        omega
      · exact ⟨v, hv, fun h => hvq h.2⟩
      · exact ⟨v, hv, fun h => hvq h.2⟩
      · refine ⟨v, hv, fun h => ?_⟩
        have := ((mem_YS A).mp hY).2
        have := (mem_WS A).mp h.1
        omega
  rw [eOld, eNew, eQ, eWQ]
  exact abs_step (Meets e (ZS A I \ A q)) (Meets e (ZS A I ∩ A q)) (Meets e (WS A I \ A q))
    (Meets e (WS A I ∩ A q)) B C M h1 h2 h3

end Step

section Asm

variable {p : ℕ} (A : Fin p → Finset V)

theorem d_compl' (H : HyperKCut.Structure.Hypergraph V) (X : Finset V) : d H Xᶜ = d H X := by
  unfold d
  congr 1
  apply Multiset.filter_congr
  intro e _
  rw [compl_compl]
  exact and_comm

theorem sig_step (H : HyperKCut.Structure.Hypergraph V) {I : Finset (Fin p)} {q : Fin p}
    (hq : q ∉ I) : sig A H (insert q I) + d H (WS A I ∩ A q) ≤ sig A H I + d H (A q) := by
  unfold sig
  rw [d_eq_sum, d_eq_sum, ← msum_add, ← msum_add]
  exact msum_le _ _ _ (fun e _ => step_edge A hq e)

theorem sig_empty (H : HyperKCut.Structure.Hypergraph V) : sig A H ∅ = 0 := by
  unfold sig
  have : ∀ e ∈ H.edges, lamE A ∅ e = 0 := by
    intro e _
    have hW : ¬ Meets e (WS A ∅) := by
      rw [meets_iff]
      rintro ⟨v, _, hv⟩
      rw [mem_WS] at hv
      simp [cnt] at hv
    have hm : mC A ∅ e = 0 := by simp [mC]
    unfold lamE lam
    rw [hm, if_neg hW]
    split_ifs <;> omega
  rw [Multiset.map_congr rfl this]
  simp

theorem WS_empty_inter (q : Fin p) : WS A {q} ∩ A q ⊆ WS A {q} := Finset.inter_subset_left

theorem WS_singleton_empty (a : Fin p) : WS A {a} = ∅ := by
  ext v
  simp only [mem_WS, Finset.notMem_empty, iff_false, not_le]
  unfold cnt
  have : (({a} : Finset (Fin p)).filter (fun i => v ∈ A i)).card ≤ 1 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  omega

/-- Lemma 3.2: the σ-value is at most `d(A a) + d(A b)`. -/
theorem sig_le (H : HyperKCut.Structure.Hypergraph V) (U : Finset V)
    (hUA : ∀ i, Uᶜ ⊆ A i)
    (hmin : ∀ q : Fin p, ∀ B : Finset V, (∀ v, v ∉ B → v ∈ A q) → Disjoint B Uᶜ →
      d H (A q)ᶜ ≤ d H B)
    (a b : Fin p) (hab : a ≠ b) :
    sig A H Finset.univ ≤ d H (A a) + d H (A b) := by
  have s1 : sig A H {a} ≤ d H (A a) := by
    have := sig_step A H (I := ∅) (q := a) (Finset.notMem_empty a)
    rw [sig_empty] at this
    have h : insert a (∅ : Finset (Fin p)) = {a} := rfl
    rw [h] at this
    omega
  have s2 : sig A H {a, b} ≤ d H (A a) + d H (A b) := by
    have hb : b ∉ ({a} : Finset (Fin p)) := by simpa using Ne.symm hab
    have := sig_step A H hb
    rw [WS_singleton_empty, Finset.empty_inter] at this
    have h : insert b ({a} : Finset (Fin p)) = {a, b} := Finset.pair_comm b a
    rw [h] at this
    omega
  have key : ∀ T : Finset (Fin p), a ∉ T → b ∉ T →
      sig A H (T ∪ {a, b}) ≤ d H (A a) + d H (A b) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _ _; simpa using s2
    | insert q T hqT ih =>
      intro haT hbT
      have hqa : q ≠ a := fun h => haT (h ▸ Finset.mem_insert_self q T)
      have hqb : q ≠ b := fun h => hbT (h ▸ Finset.mem_insert_self q T)
      have ih' := ih (fun h => haT (Finset.mem_insert_of_mem h))
        (fun h => hbT (Finset.mem_insert_of_mem h))
      have hq : q ∉ T ∪ {a, b} := by
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hqT, hqa, hqb⟩
      have hs := sig_step A H hq
      have hd : d H (A q) ≤ d H (WS A (T ∪ {a, b}) ∩ A q) := by
        rw [← d_compl' H (A q), ← d_compl' H (WS A (T ∪ {a, b}) ∩ A q)]
        apply hmin q
        · intro v hv
          rw [Finset.mem_compl, not_not] at hv
          exact (Finset.mem_inter.mp hv).2
        · rw [Finset.disjoint_left]
          intro v hv hvU
          rw [Finset.mem_compl] at hv
          apply hv
          refine Finset.mem_inter.mpr ⟨?_, hUA q hvU⟩
          rw [mem_WS]
          unfold cnt
          have hsub : ({a, b} : Finset (Fin p)) ⊆
              (T ∪ {a, b}).filter (fun i => v ∈ A i) := by
            intro i hi
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_union_right _ hi, hUA i hvU⟩
          have := Finset.card_le_card hsub
          rw [Finset.card_pair hab] at this
          exact this
      rw [Finset.insert_union]
      omega
  have := key (Finset.univ \ {a, b}) (by simp) (by simp)
  rwa [Finset.sdiff_union_of_subset (Finset.subset_univ _)] at this

/-- choose `r` indices with small total weight -/
theorem choose_J (n : Fin p → ℕ) (r : ℕ) (hr : 2 * r ≤ p) :
    ∃ J : Finset (Fin p), J.card = r ∧ 2 * ∑ i ∈ J, n i ≤ ∑ i, n i := by
  have hne : (Finset.univ.powersetCard r : Finset (Finset (Fin p))).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨J, hJ, hmin⟩ := Finset.exists_min_image _ (fun J => ∑ i ∈ J, n i) hne
  rw [Finset.mem_powersetCard] at hJ
  refine ⟨J, hJ.2, ?_⟩
  have hswap : ∀ i ∈ J, ∀ l ∉ J, n i ≤ n l := by
    intro i hi l hl
    by_contra hlt
    push_neg at hlt
    have hmem : insert l (J.erase i) ∈ (Finset.univ.powersetCard r : Finset (Finset (Fin p))) := by
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_insert_of_notMem (fun h => hl (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem hi, hJ.2]
      have : 0 < r := by rw [← hJ.2]; exact Finset.card_pos.mpr ⟨i, hi⟩
      omega
    have h1 := hmin _ hmem
    rw [Finset.sum_insert (fun h => hl (Finset.mem_of_mem_erase h))] at h1
    have h2 := Finset.add_sum_erase J n hi
    omega
  have hcard : r ≤ (Finset.univ \ J).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      hJ.2]
    omega
  obtain ⟨L, hL, hLc⟩ := Finset.exists_subset_card_eq hcard
  have hJL : Disjoint J L := by
    rw [Finset.disjoint_left]
    intro i hi hiL
    exact (Finset.mem_sdiff.mp (hL hiL)).2 hi
  have hup : ∑ i ∈ J, n i ≤ J.card * J.sup n := by
    have := Finset.sum_le_card_nsmul J n (J.sup n) (fun i hi => Finset.le_sup hi)
    simpa using this
  have hlow : L.card * J.sup n ≤ ∑ i ∈ L, n i := by
    have := Finset.card_nsmul_le_sum L n (J.sup n) (fun l hl => Finset.sup_le
      (fun i hi => hswap i hi l (Finset.mem_sdiff.mp (hL hl)).2))
    simpa using this
  have htot : ∑ i ∈ J, n i + ∑ i ∈ L, n i ≤ ∑ i, n i := by
    rw [← Finset.sum_union hJL]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [hLc, ← hJ.2] at hlow
  omega

end Asm

theorem mem_finf {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → Finset V) (v : V) :
    v ∈ s.inf f ↔ ∀ i ∈ s, v ∈ f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.inf_eq_inter, Finset.mem_inter, ih]
    simp

theorem abs33 (m : ℕ) (w z cr jj : Prop) [Decidable w] [Decidable z] [Decidable cr]
    [Decidable jj] (hcr : cr → (2 ≤ m ∨ (m = 1 ∧ jj ∧ (w ∨ z)))) :
    2 * (if cr then 1 else 0) + (if m = 1 ∧ (w ↔ ¬ z) then 1 else 0) +
        (if m = 0 ∧ w ∧ z then 1 else 0) ≤
      lam m w z + 2 * (if m = 1 ∧ jj ∧ (w ↔ ¬ z) then 1 else 0) := by
  unfold lam
  by_cases hc : cr
  · have h := hcr hc
    by_cases a : w <;> by_cases b : z <;> by_cases c : jj <;>
      simp only [hc, a, b, c, true_or, or_true, false_or, or_false, true_and, and_true,
        false_and, and_false, not_true_eq_false, not_false_eq_true, iff_true, iff_false,
        true_iff, false_iff, if_true, if_false, ite_true, ite_false] at h ⊢ <;>
      (try split_ifs) <;> omega
  · by_cases a : w <;> by_cases b : z <;> by_cases c : jj <;>
      simp only [hc, a, b, c, true_or, or_true, false_or, or_false, true_and, and_true,
        false_and, and_false, not_true_eq_false, not_false_eq_true, iff_true, iff_false,
        true_iff, false_iff, if_true, if_false, ite_true, ite_false] <;>
      (try split_ifs) <;> omega

section Final

variable {p : ℕ} (A : Fin p → Finset V)

theorem mC_two {e : Finset V} {i j : Fin p} (hij : i ≠ j) (hi : Meets e (YS A Finset.univ i))
    (hj : Meets e (YS A Finset.univ j)) : 2 ≤ mC A Finset.univ e := by
  unfold mC
  have : ({i, j} : Finset (Fin p)) ⊆
      Finset.univ.filter (fun l => Meets e (YS A Finset.univ l)) := by
    intro l hl
    rw [Finset.mem_insert, Finset.mem_singleton] at hl
    rw [Finset.mem_filter]
    rcases hl with rfl | rfl
    · exact ⟨Finset.mem_univ _, hi⟩
    · exact ⟨Finset.mem_univ _, hj⟩
  have h := Finset.card_le_card this
  rw [Finset.card_pair hij] at h
  exact h

theorem mC_pos {e : Finset V} {i : Fin p} (hi : Meets e (YS A Finset.univ i)) :
    1 ≤ mC A Finset.univ e := by
  unfold mC
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

theorem mC_one {e : Finset V} (h : mC A Finset.univ e = 1) :
    ∃ i0, Meets e (YS A Finset.univ i0) ∧ ∀ i, Meets e (YS A Finset.univ i) → i = i0 := by
  unfold mC at h
  obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp h
  refine ⟨i0, ?_, fun i hi => ?_⟩
  · have : i0 ∈ Finset.univ.filter (fun l => Meets e (YS A Finset.univ l)) := by
      rw [hi0]; exact Finset.mem_singleton_self i0
    exact (Finset.mem_filter.mp this).2
  · have : i ∈ Finset.univ.filter (fun l => Meets e (YS A Finset.univ l)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    rw [hi0, Finset.mem_singleton] at this
    exact this

/-- the indicator of a "type 1" hyperedge for index `i` -/
def t1 (e : Finset V) (i : Fin p) : ℕ :=
  if mC A Finset.univ e = 1 ∧ Meets e (YS A Finset.univ i) ∧
    (Meets e (WS A Finset.univ) ↔ ¬ Meets e (ZS A Finset.univ)) then 1 else 0

theorem sum_t1 (e : Finset V) (s : Finset (Fin p)) :
    ∑ i ∈ s, t1 A e i = if mC A Finset.univ e = 1 ∧
      (∃ i ∈ s, Meets e (YS A Finset.univ i)) ∧
      (Meets e (WS A Finset.univ) ↔ ¬ Meets e (ZS A Finset.univ)) then 1 else 0 := by
  by_cases hm : mC A Finset.univ e = 1
  · obtain ⟨i0, hi0, huniq⟩ := mC_one A hm
    have h1 : ∀ i ∈ s, t1 A e i = if i0 = i then (if Meets e (WS A Finset.univ) ↔
        ¬ Meets e (ZS A Finset.univ) then 1 else 0) else 0 := by
      intro i _
      unfold t1
      by_cases hi : i0 = i
      · subst hi
        rw [if_pos rfl]
        by_cases hwz : Meets e (WS A Finset.univ) ↔ ¬ Meets e (ZS A Finset.univ)
        · rw [if_pos ⟨hm, hi0, hwz⟩, if_pos hwz]
        · rw [if_neg (fun h => hwz h.2.2), if_neg hwz]
      · rw [if_neg hi, if_neg (fun h => hi (huniq i h.2.1).symm)]
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq]
    by_cases hs : i0 ∈ s
    · rw [if_pos hs]
      by_cases hwz : Meets e (WS A Finset.univ) ↔ ¬ Meets e (ZS A Finset.univ)
      · rw [if_pos hwz, if_pos ⟨hm, ⟨i0, hs, hi0⟩, hwz⟩]
      · rw [if_neg hwz, if_neg (fun h => hwz h.2.2)]
    · rw [if_neg hs, if_neg]
      rintro ⟨_, ⟨i, hi, hmi⟩, _⟩
      exact hs (huniq i hmi ▸ hi)
  · rw [if_neg (fun h => hm h.1)]
    apply Finset.sum_eq_zero
    intro i _
    unfold t1
    exact if_neg (fun h => hm h.1)

theorem edge33 (J : Finset (Fin p)) (e : Finset V) (cr : Prop) [Decidable cr]
    (hcr : cr → (∃ i ∈ J, Meets e (YS A Finset.univ i)) ∧
      (2 ≤ mC A Finset.univ e ∨ Meets e (WS A Finset.univ) ∨ Meets e (ZS A Finset.univ))) :
    2 * (if cr then 1 else 0) + ∑ i, t1 A e i +
        (if mC A Finset.univ e = 0 ∧ Meets e (WS A Finset.univ) ∧ Meets e (ZS A Finset.univ)
          then 1 else 0) ≤
      lamE A Finset.univ e + 2 * ∑ i ∈ J, t1 A e i := by
  rw [sum_t1, sum_t1]
  unfold lamE
  have key := abs33 (mC A Finset.univ e) (Meets e (WS A Finset.univ))
    (Meets e (ZS A Finset.univ)) cr (∃ i ∈ J, Meets e (YS A Finset.univ i)) (by
      intro hc
      obtain ⟨hJ, h2⟩ := hcr hc
      by_cases hm : 2 ≤ mC A Finset.univ e
      · exact Or.inl hm
      · right
        have hJ' := hJ
        obtain ⟨i, _, hi⟩ := hJ'
        have := mC_pos A hi
        refine ⟨by omega, hJ, ?_⟩
        rcases h2 with h | h
        · exact absurd h hm
        · exact h)
  have e1 : (if mC A Finset.univ e = 1 ∧ (∃ i ∈ (Finset.univ : Finset (Fin p)),
      Meets e (YS A Finset.univ i)) ∧
      (Meets e (WS A Finset.univ) ↔ ¬ Meets e (ZS A Finset.univ)) then 1 else 0 : ℕ) =
      if mC A Finset.univ e = 1 ∧
        (Meets e (WS A Finset.univ) ↔ ¬ Meets e (ZS A Finset.univ)) then 1 else 0 := by
    apply ind_congr
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      obtain ⟨i0, hi0, _⟩ := mC_one A h1
      exact ⟨h1, ⟨i0, Finset.mem_univ _, hi0⟩, h3⟩
  rw [e1]
  exact key

/-- the per-edge Lemma 3.3 inequality summed over all hyperedges -/
theorem sum33 (H : HyperKCut.Structure.Hypergraph V) (J : Finset (Fin p))
    (cr : Finset V → Prop) [DecidablePred cr]
    (hcr : ∀ e, cr e → (∃ i ∈ J, Meets e (YS A Finset.univ i)) ∧
      (2 ≤ mC A Finset.univ e ∨ Meets e (WS A Finset.univ) ∨ Meets e (ZS A Finset.univ))) :
    2 * H.edges.countP cr + ∑ i, (H.edges.map (fun e => t1 A e i)).sum +
        (H.edges.map (fun e => if mC A Finset.univ e = 0 ∧ Meets e (WS A Finset.univ) ∧
          Meets e (ZS A Finset.univ) then 1 else 0)).sum ≤
      sig A H Finset.univ + 2 * ∑ i ∈ J, (H.edges.map (fun e => t1 A e i)).sum := by
  rw [countP_eq_sum, ← msum_finset, ← msum_finset, ← Multiset.sum_map_mul_left,
    ← Multiset.sum_map_mul_left]
  unfold sig
  rw [← msum_add, ← msum_add, ← msum_add]
  exact msum_le _ _ _ (fun e _ => edge33 A J e (cr e) (hcr e))

end Final

/-- Theorem 1.5 (both conclusions; strict when an extra `W`–`Z` hyperedge exists). -/
theorem thm15 (H : HyperKCut.Structure.Hypergraph V) (k p : ℕ)
    (hk : 2 ≤ k) (hp : 2 * k - 2 ≤ p)
    (R U : Finset V) (hR : R.Nonempty) (hRU : R ⊂ U)
    (u : Fin p → V)
    (hu : ∀ i, u i ∈ U \ R)
    (A : Fin p → Finset V)
    (hA : ∀ i, IsMinTerminalCut H
      (((Finset.univ.image u) ∪ R).erase (u i)) Uᶜ (A i)ᶜ)
    (hui : ∀ i, u i ∈ A i)
    (huj : ∀ i j, i ≠ j → u i ∉ A j) (ex : ℕ)
    (hex : ex ≤ (H.edges.map (fun e => if mC A Finset.univ e = 0 ∧
          Meets e (WS A Finset.univ) ∧ Meets e (ZS A Finset.univ) then 1 else 0)).sum) :
    ∃ P : Fin k → Finset V, IsPartition P ∧
      Uᶜ ⊂ P ⟨k - 1, by omega⟩ ∧
      ∀ i j : Fin p, i ≠ j → 2 * cost H P + ex ≤ d H (A i) + d H (A j) := by
  -- basic facts
  have hUA : ∀ i, Uᶜ ⊆ A i := by
    intro i v hv
    by_contra hvA
    exact Finset.disjoint_left.mp (hA i).1.2 (Finset.mem_compl.mpr hvA) hv
  have hRA : ∀ i, ∀ r ∈ R, r ∉ A i := by
    intro i r hr hrA
    have hne : r ≠ u i := fun h => (Finset.mem_sdiff.mp (hu i)).2 (h ▸ hr)
    have : r ∈ ((Finset.univ.image u) ∪ R).erase (u i) :=
      Finset.mem_erase.mpr ⟨hne, Finset.mem_union_right _ hr⟩
    exact Finset.mem_compl.mp ((hA i).1.1 this) hrA
  have hmin : ∀ q : Fin p, ∀ B : Finset V, (∀ v, v ∉ B → v ∈ A q) → Disjoint B Uᶜ →
      d H (A q)ᶜ ≤ d H B := by
    intro q B hB hBd
    apply (hA q).2 B
    refine ⟨?_, hBd⟩
    intro v hv
    by_contra hvB
    exact Finset.mem_compl.mp ((hA q).1.1 hv) (hB v hvB)
  have hp2 : 2 ≤ p := by omega
  -- vertices of `Y`
  have hcnt_u : ∀ i, cnt A Finset.univ (u i) = 1 := by
    intro i
    unfold cnt
    rw [Finset.card_eq_one]
    refine ⟨i, ?_⟩
    ext l
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hl⟩
      by_contra hli
      exact huj i l (Ne.symm hli) hl
    · rintro rfl
      exact ⟨Finset.mem_univ _, hui l⟩
  have huY : ∀ i, u i ∈ YS A Finset.univ i := fun i => (mem_YS A).mpr ⟨hui i, hcnt_u i⟩
  obtain ⟨r0, hr0⟩ := hR
  have hr0Z : r0 ∈ ZS A Finset.univ := by
    rw [mem_ZS]
    unfold cnt
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    exact hRA i r0 hr0
  have hUW : Uᶜ ⊆ WS A Finset.univ := by
    intro v hv
    rw [mem_WS]
    unfold cnt
    have hsub : ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin p)) ⊆
        Finset.univ.filter (fun i => v ∈ A i) := by
      intro i _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUA i hv⟩
    have h := Finset.card_le_card hsub
    rw [Finset.card_pair (by simp [Fin.ext_iff])] at h
    exact h
  -- choose the indices
  obtain ⟨J, hJc, hJs⟩ := choose_J (fun i => (H.edges.map (fun e => t1 A e i)).sum) (k - 1)
    (by omega)
  obtain ⟨emb, hembdef⟩ : ∃ f, f = J.orderEmbOfFin hJc := ⟨_, rfl⟩
  have hemb : ∀ t, emb t ∈ J := by
    intro t
    rw [hembdef]
    exact Finset.orderEmbOfFin_mem J hJc t
  have hembs : ∀ i ∈ J, ∃ t, emb t = i := by
    intro i hi
    have : i ∈ Set.range emb := by
      rw [hembdef, Finset.range_orderEmbOfFin]
      exact hi
    exact this
  let Rest : Finset V := (J.biUnion (YS A Finset.univ))ᶜ
  let P : Fin k → Finset V := fun t =>
    if h : t.val < k - 1 then YS A Finset.univ (emb ⟨t.val, h⟩) else Rest
  have hPlast : P ⟨k - 1, by omega⟩ = Rest := by
    show (if h : k - 1 < k - 1 then _ else Rest) = Rest
    rw [dif_neg (lt_irrefl _)]
  have hPlt : ∀ t : Fin k, ∀ h : t.val < k - 1, P t = YS A Finset.univ (emb ⟨t.val, h⟩) := by
    intro t h
    show (if h : t.val < k - 1 then _ else Rest) = _
    rw [dif_pos h]
  have hPge : ∀ t : Fin k, ¬ t.val < k - 1 → P t = Rest := by
    intro t h
    show (if h : t.val < k - 1 then _ else Rest) = _
    rw [dif_neg h]
  have hYRest : ∀ i ∈ J, Disjoint (YS A Finset.univ i) Rest := by
    intro i hi
    rw [Finset.disjoint_left]
    intro v hv hvR
    exact Finset.mem_compl.mp hvR (Finset.mem_biUnion.mpr ⟨i, hi, hv⟩)
  have hZRest : ZS A Finset.univ ⊆ Rest := by
    intro v hv
    show v ∈ (J.biUnion (YS A Finset.univ))ᶜ
    rw [Finset.mem_compl]
    intro hvB
    obtain ⟨i, _, hvi⟩ := Finset.mem_biUnion.mp hvB
    have h1 := (mem_YS A).mp hvi
    have h2 := (mem_ZS A).mp hv
    omega
  have hWRest : WS A Finset.univ ⊆ Rest := by
    intro v hv
    show v ∈ (J.biUnion (YS A Finset.univ))ᶜ
    rw [Finset.mem_compl]
    intro hvB
    obtain ⟨i, _, hvi⟩ := Finset.mem_biUnion.mp hvB
    have h1 := (mem_YS A).mp hvi
    have h2 := (mem_WS A).mp hv
    omega
  have hYdisj : ∀ i j : Fin p, i ≠ j → Disjoint (YS A Finset.univ i) (YS A Finset.univ j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro v hi hj
    rw [mem_YS] at hi hj
    exact hij (cnt_one_unique A hi.2 (Finset.mem_univ i) hi.1 (Finset.mem_univ j) hj.1)
  -- partition
  have hpart : IsPartition P := by
    refine ⟨?_, ?_, ?_⟩
    · intro t
      by_cases h : t.val < k - 1
      · rw [hPlt t h]
        exact ⟨_, huY _⟩
      · rw [hPge t h]
        exact ⟨r0, hZRest hr0Z⟩
    · intro s t hst
      by_cases hs : s.val < k - 1 <;> by_cases ht : t.val < k - 1
      · rw [hPlt s hs, hPlt t ht]
        apply hYdisj
        intro heq
        apply hst
        have := emb.injective heq
        rw [Fin.ext_iff] at this ⊢
        simpa using this
      · rw [hPlt s hs, hPge t ht]
        exact hYRest _ (hemb _)
      · rw [hPge s hs, hPlt t ht]
        exact (hYRest _ (hemb _)).symm
      · exfalso
        apply hst
        rw [Fin.ext_iff]
        omega
    · intro v
      by_cases hv : v ∈ J.biUnion (YS A Finset.univ)
      · obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
        obtain ⟨t, rfl⟩ := hembs i hi
        refine ⟨⟨t.val, by omega⟩, ?_⟩
        rw [hPlt ⟨t.val, by omega⟩ t.isLt]
        exact hvi
      · refine ⟨⟨k - 1, by omega⟩, ?_⟩
        rw [hPlast]
        exact Finset.mem_compl.mpr hv
  refine ⟨P, hpart, ?_, ?_⟩
  · rw [hPlast]
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hUW.trans hWRest, ?_⟩
    intro heq
    have : r0 ∈ Rest := hZRest hr0Z
    rw [← heq, Finset.mem_compl] at this
    exact this (hRU.1 hr0)
  · intro i j hij
    have hsig := sig_le A H U hUA hmin i j hij
    -- the crossing predicate
    have hcr : ∀ e, (∃ s t, s ≠ t ∧ Meets e (P s) ∧ Meets e (P t)) →
        (∃ i ∈ J, Meets e (YS A Finset.univ i)) ∧
        (2 ≤ mC A Finset.univ e ∨ Meets e (WS A Finset.univ) ∨ Meets e (ZS A Finset.univ)) := by
      rintro e ⟨s, t, hst, hs, ht⟩
      -- the Rest case
      have hrest : Meets e Rest → (2 ≤ mC A Finset.univ e ∨ Meets e (WS A Finset.univ) ∨
          Meets e (ZS A Finset.univ)) ∨ ∃ l, l ∉ J ∧ Meets e (YS A Finset.univ l) := by
        intro hm
        rw [meets_iff] at hm
        obtain ⟨v, hv, hvR⟩ := hm
        rcases Nat.lt_or_ge (cnt A Finset.univ v) 1 with h | h
        · exact Or.inl (Or.inr (Or.inr (meets_iff.mpr ⟨v, hv, (mem_ZS A).mpr (by omega)⟩)))
        · rcases Nat.lt_or_ge (cnt A Finset.univ v) 2 with h' | h'
          · obtain ⟨l, _, hvl⟩ := cnt_one_exists A (by omega : cnt A Finset.univ v = 1)
            have hY : v ∈ YS A Finset.univ l := (mem_YS A).mpr ⟨hvl, by omega⟩
            refine Or.inr ⟨l, fun hl => ?_, meets_iff.mpr ⟨v, hv, hY⟩⟩
            exact Finset.mem_compl.mp hvR (Finset.mem_biUnion.mpr ⟨l, hl, hY⟩)
          · exact Or.inl (Or.inr (Or.inl (meets_iff.mpr ⟨v, hv, (mem_WS A).mpr h'⟩)))
      have main : ∀ s t : Fin k, s ≠ t → s.val < k - 1 → Meets e (P s) → Meets e (P t) →
          (∃ i ∈ J, Meets e (YS A Finset.univ i)) ∧
          (2 ≤ mC A Finset.univ e ∨ Meets e (WS A Finset.univ) ∨
            Meets e (ZS A Finset.univ)) := by
        intro s t hst hs hms hmt
        rw [hPlt s hs] at hms
        refine ⟨⟨_, hemb _, hms⟩, ?_⟩
        by_cases ht : t.val < k - 1
        · rw [hPlt t ht] at hmt
          left
          apply mC_two A _ hms hmt
          intro heq
          apply hst
          have := emb.injective heq
          rw [Fin.ext_iff] at this ⊢
          simpa using this
        · rw [hPge t ht] at hmt
          rcases hrest hmt with h | ⟨l, hl, hml⟩
          · exact h
          · left
            apply mC_two A _ hms hml
            intro heq
            exact hl (heq ▸ hemb _)
      by_cases hs' : s.val < k - 1
      · exact main s t hst hs' hs ht
      · by_cases ht' : t.val < k - 1
        · exact main t s (Ne.symm hst) ht' ht hs
        · exfalso
          apply hst
          rw [Fin.ext_iff]
          omega
    have hsum := sum33 A H J (fun e => ∃ s t, s ≠ t ∧ Meets e (P s) ∧ Meets e (P t)) hcr
    have hcost : cost H P = H.edges.countP
        (fun e => ∃ s t, s ≠ t ∧ Meets e (P s) ∧ Meets e (P t)) := by
      unfold cost
      rw [Multiset.countP_eq_card_filter]
    rw [hcost]
    omega

theorem apply15 (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k) (U : Finset V)
    (hopt : IsOptKCutValue H k (d H U)) (q : ℕ) (hq : 2 * k - 2 ≤ q)
    (v : Fin q → V) (R : Finset V) (hR : R.Nonempty) (hRU : R ⊂ U)
    (hv : ∀ t, v t ∈ U \ R) (B : Fin q → Finset V)
    (hB : ∀ t, IsMinTerminalCut H (((Finset.univ.image v) ∪ R).erase (v t)) Uᶜ (B t))
    (hvB : ∀ t, v t ∉ B t) (hvB2 : ∀ t t', t ≠ t' → v t ∈ B t') (ex : ℕ)
    (hex : ex ≤ (H.edges.map (fun e => if mC (fun t => (B t)ᶜ) Finset.univ e = 0 ∧
      Meets e (WS (fun t => (B t)ᶜ) Finset.univ) ∧
      Meets e (ZS (fun t => (B t)ᶜ) Finset.univ) then 1 else 0)).sum) :
    ∀ t t', t ≠ t' → 2 * d H U + ex ≤ d H (B t) + d H (B t') := by
  obtain ⟨P, hP1, _, hP3⟩ := thm15 H k q hk hq R U hR hRU v hv (fun t => (B t)ᶜ)
    (fun t => by simpa using hB t) (fun t => Finset.mem_compl.mpr (hvB t))
    (fun t t' h => by simpa using hvB2 t t' h) ex hex
  intro t t' h
  have h1 := hP3 t t' h
  simp only [d_compl'] at h1
  have h2 := hopt.2 P hP1
  omega

theorem cor22 (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (S : Finset V) (hS : IsMinTransversal H U S)
    (p : ℕ) (hp : 2 * k ≤ p) (u : Fin p → V) (hu : Function.Injective u)
    (hSu : S = Finset.univ.image u)
    (Hs : Finset V → Finset V)
    (hHs : ∀ X : Finset V, X ⊆ U → X.Nonempty → IsSourceMinMinTerminalCut H X Uᶜ (Hs X))
    (i j : Fin p) : u i ∉ Hs ((S.erase (u i)).erase (u j)) ∧
      u j ∉ Hs ((S.erase (u i)).erase (u j)) := by
  have hSU : S ⊆ U := hS.1
  have hcard : S.card = p := by
    rw [hSu, Finset.card_image_of_injective _ hu, Finset.card_univ, Fintype.card_fin]
  have hci := Finset.pred_card_le_card_erase (s := S) (a := u i)
  have hcj := Finset.pred_card_le_card_erase (s := S) (a := u j)
  have hcij := Finset.pred_card_le_card_erase (s := S.erase (u i)) (a := u j)
  have hXi : S.erase (u i) ⊆ U := (Finset.erase_subset _ _).trans hSU
  have hXj : S.erase (u j) ⊆ U := (Finset.erase_subset _ _).trans hSU
  have hXij : (S.erase (u i)).erase (u j) ⊆ U := (Finset.erase_subset _ _).trans hXi
  have hne_i : (S.erase (u i)).Nonempty := by rw [← Finset.card_pos]; omega
  have hne_j : (S.erase (u j)).Nonempty := by rw [← Finset.card_pos]; omega
  have hne_ij : ((S.erase (u i)).erase (u j)).Nonempty := by rw [← Finset.card_pos]; omega
  have h1 : Hs ((S.erase (u i)).erase (u j)) ⊆ Hs (S.erase (u i)) :=
    mono H _ _ Uᶜ _ _ (Finset.erase_subset _ _) (hHs _ hXij hne_ij) (hHs _ hXi hne_i)
  have hcomm : (S.erase (u i)).erase (u j) = (S.erase (u j)).erase (u i) :=
    Finset.erase_right_comm
  have h2 : Hs ((S.erase (u i)).erase (u j)) ⊆ Hs (S.erase (u j)) := by
    have := mono H ((S.erase (u j)).erase (u i)) (S.erase (u j)) Uᶜ _ _ (Finset.erase_subset _ _)
      (hHs _ (by rw [← hcomm]; exact hXij) (by rw [← hcomm]; exact hne_ij)) (hHs _ hXj hne_j)
    rw [hcomm]
    exact this
  have ci := (claim21_full H k hk U S hS p hp u hu hSu Hs hHs i).2
  have cj := (claim21_full H k hk U S hS p hp u hu hSu Hs hHs j).2
  rw [Finset.mem_compl] at ci cj
  exact ⟨fun h => ci (h1 h), fun h => cj (h2 h)⟩

theorem enum_fin {p : ℕ} (T : Finset (Fin p)) :
    ∃ emb : Fin T.card → Fin p, Function.Injective emb ∧ (∀ t, emb t ∈ T) ∧
      ∀ i ∈ T, ∃ t, emb t = i := by
  refine ⟨T.orderEmbOfFin rfl, (T.orderEmbOfFin rfl).injective,
    fun t => Finset.orderEmbOfFin_mem T rfl t, fun i hi => ?_⟩
  have : i ∈ Set.range (T.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hi
  exact this

/-- the main inequality of Claim 2.3 -/
theorem c23_core (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (hopt : IsOptKCutValue H k (d H U))
    (S : Finset V) (hS : IsMinTransversal H U S)
    (p : ℕ) (hp : 2 * k ≤ p) (u : Fin p → V) (hu : Function.Injective u)
    (hSu : S = Finset.univ.image u)
    (Hs : Finset V → Finset V)
    (hHs : ∀ X : Finset V, X ⊆ U → X.Nonempty → IsSourceMinMinTerminalCut H X Uᶜ (Hs X))
    (a b : Fin p) (hab : a ≠ b) : d H U ≤ d H (Hs ((S.erase (u a)).erase (u b))) := by
  have hSU : S ⊆ U := hS.1
  have huS : ∀ i, u i ∈ S := fun i => by rw [hSu]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  -- choose two further indices
  have hc2 : ((Finset.univ.erase a).erase b).card = p - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨l, hl⟩ := Finset.card_pos.mp (by omega : 0 < ((Finset.univ.erase a).erase b).card)
  have hla : l ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
  have hlb : l ≠ b := (Finset.mem_erase.mp hl).1
  have hc3 : (((Finset.univ.erase a).erase b).erase l).card = p - 3 := by
    rw [Finset.card_erase_of_mem hl, hc2]
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < (((Finset.univ.erase a).erase b).erase l).card)
  have hjl : j ≠ l := (Finset.mem_erase.mp hj).1
  have hjb : j ≠ b := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
  have hja : j ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).2).1
  -- the index set
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin p), T = (Finset.univ.erase a).erase l := ⟨_, rfl⟩
  have hTmem : ∀ i, i ∈ T ↔ i ≠ a ∧ i ≠ l := by
    intro i
    rw [hT, Finset.mem_erase, Finset.mem_erase]
    simp only [Finset.mem_univ, and_true]
    exact and_comm
  have hTc : T.card = p - 2 := by
    rw [hT, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hla, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨emb, hemb_inj, hemb, hembs⟩ := enum_fin T
  have hvinj : Function.Injective (fun t => u (emb t)) := fun x y h => hemb_inj (hu h)
  have hterm : ∀ t, ((Finset.univ.image (fun t => u (emb t))) ∪ {u l}).erase (u (emb t)) =
      (S.erase (u a)).erase (u (emb t)) := by
    intro t
    ext x
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_singleton, hSu]
    constructor
    · rintro ⟨hx, ⟨t', rfl⟩ | rfl⟩
      · refine ⟨hx, fun h => ((hTmem _).mp (hemb t')).1 (hu h), ⟨_, rfl⟩⟩
      · exact ⟨hx, fun h => hla (hu h), ⟨l, rfl⟩⟩
    · rintro ⟨hx, hxa, ⟨i, rfl⟩⟩
      refine ⟨hx, ?_⟩
      by_cases hil : i = l
      · right; rw [hil]
      · left
        have hia : i ≠ a := fun h => hxa (by rw [h])
        obtain ⟨t', ht'⟩ := hembs i ((hTmem i).mpr ⟨hia, hil⟩)
        exact ⟨t', by rw [ht']⟩
  have hX : ∀ t, (S.erase (u a)).erase (u (emb t)) ⊆ U :=
    fun t => (Finset.erase_subset _ _).trans ((Finset.erase_subset _ _).trans hSU)
  have hcardS : S.card = p := by
    rw [hSu, Finset.card_image_of_injective _ hu, Finset.card_univ, Fintype.card_fin]
  have hXne : ∀ t, ((S.erase (u a)).erase (u (emb t))).Nonempty := by
    intro t
    have h1 := Finset.pred_card_le_card_erase (s := S) (a := u a)
    have h2 := Finset.pred_card_le_card_erase (s := S.erase (u a)) (a := u (emb t))
    rw [← Finset.card_pos]
    omega
  have key := apply15 H k hk U hopt T.card (by omega) (fun t => u (emb t)) {u l}
    (Finset.singleton_nonempty _)
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr (hSU (huS l)), by
      intro h
      have : u a ∈ ({u l} : Finset V) := by rw [h]; exact hSU (huS a)
      rw [Finset.mem_singleton] at this
      exact hla (hu this).symm⟩)
    (fun t => Finset.mem_sdiff.mpr ⟨hSU (huS _), by
      rw [Finset.mem_singleton]
      intro h
      exact ((hTmem _).mp (hemb t)).2 (hu h)⟩)
    (fun t => Hs ((S.erase (u a)).erase (u (emb t))))
    (fun t => by
      show IsMinTerminalCut H (((Finset.univ.image (fun t => u (emb t))) ∪ {u l}).erase
        (u (emb t))) Uᶜ (Hs ((S.erase (u a)).erase (u (emb t))))
      rw [hterm t]
      exact (hHs _ (hX t) (hXne t)).1)
    (fun t => (cor22 H k hk U S hS p hp u hu hSu Hs hHs a (emb t)).2)
    (fun t t' htt => (hHs _ (hX t') (hXne t')).1.1.1 (by
      rw [Finset.mem_erase, Finset.mem_erase]
      refine ⟨fun h => htt (hemb_inj (hu h)), fun h => ((hTmem _).mp (hemb t)).1 (hu h), huS _⟩))
    0 (Nat.zero_le _)
  obtain ⟨tb, htb⟩ := hembs b ((hTmem b).mpr ⟨Ne.symm hab, Ne.symm hlb⟩)
  obtain ⟨tj, htj⟩ := hembs j ((hTmem j).mpr ⟨hja, hjl⟩)
  have hne : tb ≠ tj := fun h => hjb (by rw [← htj, ← htb, h])
  have h1 := key tb tj hne
  simp only [htb, htj] at h1
  have h2 : d H (Hs ((S.erase (u a)).erase (u j))) ≤ d H U := by
    apply (hHs ((S.erase (u a)).erase (u j)) (by rw [← htj]; exact hX tj)
      (by rw [← htj]; exact hXne tj)).1.2
    exact ⟨(Finset.erase_subset _ _).trans ((Finset.erase_subset _ _).trans hSU),
      disjoint_compl_right⟩
  omega

theorem c23_full (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (hopt : IsOptKCutValue H k (d H U))
    (S : Finset V) (hS : IsMinTransversal H U S)
    (p : ℕ) (hp : 2 * k ≤ p) (u : Fin p → V) (hu : Function.Injective u)
    (hSu : S = Finset.univ.image u)
    (Hs : Finset V → Finset V)
    (hHs : ∀ X : Finset V, X ⊆ U → X.Nonempty → IsSourceMinMinTerminalCut H X Uᶜ (Hs X))
    (i j : Fin p) : d H (Hs (S.erase (u i))) = d H U ∧
      d H U = d H (Hs ((S.erase (u i)).erase (u j))) := by
  have hSU : S ⊆ U := hS.1
  have hcardS : S.card = p := by
    rw [hSu, Finset.card_image_of_injective _ hu, Finset.card_univ, Fintype.card_fin]
  have h1 := Finset.pred_card_le_card_erase (s := S) (a := u i)
  have hXi : S.erase (u i) ⊆ U := (Finset.erase_subset _ _).trans hSU
  have hXine : (S.erase (u i)).Nonempty := by rw [← Finset.card_pos]; omega
  have hHi := hHs _ hXi hXine
  have hle1 : d H (Hs (S.erase (u i))) ≤ d H U :=
    hHi.1.2 U ⟨hXi, disjoint_compl_right⟩
  -- monotonicity in the terminal set
  have hmono : ∀ j, j ≠ i → d H (Hs ((S.erase (u i)).erase (u j))) ≤ d H (Hs (S.erase (u i))) := by
    intro j _
    have h2 := Finset.pred_card_le_card_erase (s := S.erase (u i)) (a := u j)
    have hXij : (S.erase (u i)).erase (u j) ⊆ U := (Finset.erase_subset _ _).trans hXi
    have hne : ((S.erase (u i)).erase (u j)).Nonempty := by rw [← Finset.card_pos]; omega
    exact (hHs _ hXij hne).1.2 _ ⟨(Finset.erase_subset _ _).trans hHi.1.1.1, hHi.1.1.2⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin p, b ≠ i := by
    by_cases h0 : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by rw [Fin.ext_iff] at h; simp at h; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h => by rw [Fin.ext_iff] at h; simp at h; omega⟩
  have hb1 := c23_core H k hk U hopt S hS p hp u hu hSu Hs hHs i b (Ne.symm hb)
  have hb2 := hmono b hb
  have heq : d H (Hs (S.erase (u i))) = d H U := by omega
  refine ⟨heq, ?_⟩
  by_cases hji : j = i
  · subst hji
    have : (S.erase (u j)).erase (u j) = S.erase (u j) :=
      Finset.erase_eq_of_notMem (Finset.notMem_erase _ _)
    rw [this, heq]
  · have := c23_core H k hk U hopt S hS p hp u hu hSu Hs hHs i j (Ne.symm hji)
    have := hmono j hji
    omega


end Aux_CutSetEnum_claim_2_3


open HyperKCut.Structure CutSetEnum Aux_CutSetEnum_claim_2_3 in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty)
    (hopt : IsOptKCutValue H k (d H U))
    (S : Finset V) (hS : IsMinTransversal H U S)
    (p : ℕ) (hp : 2 * k ≤ p) (u : Fin p → V) (hu : Function.Injective u)
    (hSu : S = Finset.univ.image u)
    (Hs : Finset V → Finset V)
    (hHs : ∀ X : Finset V, X ⊆ U → X.Nonempty → IsSourceMinMinTerminalCut H X Uᶜ (Hs X)) :
    ∀ i j : Fin p, d H (Hs (S.erase (u i))) = d H U ∧
      d H U = d H (Hs ((S.erase (u i)).erase (u j))) := by
  intro i j
  exact c23_full H k hk U hopt S hS p hp u hu hSu Hs hHs i j

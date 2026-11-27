-- Prove2me | solution 1 for BinaryThreeLCC.JM.eulerian_cut_dense_piece
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:05:53.59847+00:00
-- url     : https://prove2.me/submissions/d8130120-1372-4864-b15f-d0e923d0b0d8

import Mathlib
import Theorems.Thm_BinaryThreeLCC_JM_chvatal_szemeredi

set_option autoImplicit false

namespace BinaryThreeLCC.JM


namespace T4aux

section
open Classical

variable {α : Type} [DecidableEq α]

def outC (F : Finset (α × α)) (x : α) : ℕ := (F.filter (fun p => p.1 = x)).card
def inC (F : Finset (α × α)) (x : α) : ℕ := (F.filter (fun p => p.2 = x)).card
def Bal (F : Finset (α × α)) : Prop := ∀ x, outC F x = inC F x

lemma sum_outC (t : Finset (α × α)) (S : Finset α) :
    ∑ x ∈ S, outC t x = (t.filter (fun p => p.1 ∈ S)).card := by
  simp only [outC, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_ite_eq]

lemma sum_inC (t : Finset (α × α)) (S : Finset α) :
    ∑ x ∈ S, inC t x = (t.filter (fun p => p.2 ∈ S)).card := by
  simp only [inC, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_ite_eq]

lemma card_filter_split {β : Type} (t : Finset β) (P Q1 Q2 : β → Prop)
    [DecidablePred P] [DecidablePred Q1] [DecidablePred Q2]
    (h : ∀ p ∈ t, (P p ↔ Q1 p ∨ Q2 p)) (hd : ∀ p ∈ t, ¬ (Q1 p ∧ Q2 p)) :
    (t.filter P).card = (t.filter Q1).card + (t.filter Q2).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hp, hP⟩
      rcases (h p hp).1 hP with h1 | h2
      · exact Or.inl ⟨hp, h1⟩
      · exact Or.inr ⟨hp, h2⟩
    · rintro (⟨hp, h1⟩ | ⟨hp, h2⟩)
      · exact ⟨hp, (h p hp).2 (Or.inl h1)⟩
      · exact ⟨hp, (h p hp).2 (Or.inr h2)⟩
  · rw [Finset.disjoint_filter]
    intro p hp h1 h2
    exact hd p hp ⟨h1, h2⟩

lemma cross_eq (t : Finset (α × α)) (U S : Finset α) (hin : ∀ p ∈ t, p.1 ∈ U ∧ p.2 ∈ U)
    (hb : Bal t) :
    (t.filter (fun p => p.1 ∈ S ∧ p.2 ∈ U \ S)).card =
      (t.filter (fun p => p.1 ∈ U \ S ∧ p.2 ∈ S)).card := by
  have h3 : (t.filter (fun p => p.1 ∈ S)).card = (t.filter (fun p => p.2 ∈ S)).card := by
    rw [← sum_outC, ← sum_inC]
    exact Finset.sum_congr rfl (fun x _ => hb x)
  have h1 : (t.filter (fun p => p.1 ∈ S)).card = (t.filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card +
      (t.filter (fun p => p.1 ∈ S ∧ p.2 ∈ U \ S)).card := by
    apply card_filter_split
    · intro p hp
      have := (hin p hp).2
      simp only [Finset.mem_sdiff]
      tauto
    · intro p _
      simp only [Finset.mem_sdiff]
      tauto
  have h2 : (t.filter (fun p => p.2 ∈ S)).card = (t.filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card +
      (t.filter (fun p => p.1 ∈ U \ S ∧ p.2 ∈ S)).card := by
    apply card_filter_split
    · intro p hp
      have := (hin p hp).1
      simp only [Finset.mem_sdiff]
      tauto
    · intro p _
      simp only [Finset.mem_sdiff]
      tauto
  omega

lemma bal_biUnion {ι : Type} (I : Finset ι) (f : ι → Finset (α × α))
    (hd : (I : Set ι).PairwiseDisjoint f) (hb : ∀ i ∈ I, Bal (f i)) : Bal (I.biUnion f) := by
  intro x
  unfold outC inC
  rw [Finset.filter_biUnion, Finset.filter_biUnion, Finset.card_biUnion, Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun i hi => hb i hi x)
  · intro i hi j hj hij
    exact Finset.disjoint_filter_filter (hd hi hj hij)
  · intro i hi j hj hij
    exact Finset.disjoint_filter_filter (hd hi hj hij)

def SameBlock (P : Finset (Finset α)) (x y : α) : Prop := ∃ W ∈ P, x ∈ W ∧ y ∈ W
def Uncut (P : Finset (Finset α)) (s : Finset (α × α)) : Prop := ∀ p ∈ s, SameBlock P p.1 p.2

lemma block_unique {P : Finset (Finset α)} (hP : (P : Set (Finset α)).PairwiseDisjoint id)
    {W U : Finset α} (hW : W ∈ P) (hU : U ∈ P) {x : α} (hxW : x ∈ W) (hxU : x ∈ U) : W = U := by
  by_contra hne
  have := hP hW hU hne
  exact Finset.disjoint_left.1 this hxW hxU

lemma bal_restrict {P : Finset (Finset α)} (hP : (P : Set (Finset α)).PairwiseDisjoint id)
    {s : Finset (α × α)} (hs : Bal s) (hu : Uncut P s) {U : Finset α} (hU : U ∈ P) :
    Bal (s.filter (fun p => p.1 ∈ U ∧ p.2 ∈ U)) := by
  intro x
  unfold outC inC
  rw [Finset.filter_filter, Finset.filter_filter]
  by_cases hx : x ∈ U
  · have e1 : s.filter (fun p => (p.1 ∈ U ∧ p.2 ∈ U) ∧ p.1 = x) = s.filter (fun p => p.1 = x) := by
      apply Finset.filter_congr
      intro p hp
      constructor
      · exact fun h => h.2
      · intro h
        obtain ⟨W, hW, h1, h2⟩ := hu p hp
        have : W = U := block_unique hP hW hU h1 (h ▸ hx)
        subst this
        exact ⟨⟨h1, h2⟩, h⟩
    have e2 : s.filter (fun p => (p.1 ∈ U ∧ p.2 ∈ U) ∧ p.2 = x) = s.filter (fun p => p.2 = x) := by
      apply Finset.filter_congr
      intro p hp
      constructor
      · exact fun h => h.2
      · intro h
        obtain ⟨W, hW, h1, h2⟩ := hu p hp
        have : W = U := block_unique hP hW hU h2 (h ▸ hx)
        subst this
        exact ⟨⟨h1, h2⟩, h⟩
    rw [e1, e2]
    exact hs x
  · have e1 : s.filter (fun p => (p.1 ∈ U ∧ p.2 ∈ U) ∧ p.1 = x) = ∅ := by
      apply Finset.filter_false_of_mem
      rintro p - ⟨⟨h1, -⟩, h⟩
      exact hx (h ▸ h1)
    have e2 : s.filter (fun p => (p.1 ∈ U ∧ p.2 ∈ U) ∧ p.2 = x) = ∅ := by
      apply Finset.filter_false_of_mem
      rintro p - ⟨⟨-, h2⟩, h⟩
      exact hx (h ▸ h2)
    rw [e1, e2]

noncomputable def keptIn (𝒞 : Finset (Finset (α × α))) (P : Finset (Finset α)) (W : Finset α) :
    Finset (α × α) :=
  (𝒞.filter (Uncut P)).biUnion (fun s => s.filter (fun p => p.1 ∈ W ∧ p.2 ∈ W))

noncomputable def cost (𝒞 : Finset (Finset (α × α))) (P : Finset (Finset α)) : ℕ :=
  ∑ s ∈ 𝒞.filter (fun s => ¬ Uncut P s), s.card

noncomputable def sep (V : Finset α) (P : Finset (Finset α)) : ℝ :=
  ∑ W ∈ P, (W.card : ℝ) * (V.card - W.card)

lemma exists_cross_arc {𝒞 : Finset (Finset (α × α))} {P : Finset (Finset α)}
    (hP : (P : Set (Finset α)).PairwiseDisjoint id) (hbal : ∀ s ∈ 𝒞, Bal s)
    {W S : Finset α} (hW : W ∈ P) {s : Finset (α × α)} (hs𝒞 : s ∈ 𝒞) (hsu : Uncut P s)
    (hcut : ¬ Uncut (insert S (insert (W \ S) (P.erase W))) s) :
    ∃ q ∈ s, q ∈ keptIn 𝒞 P W ∧ q.1 ∈ S ∧ q.2 ∈ W \ S := by
  simp only [Uncut, not_forall] at hcut
  obtain ⟨p, hp, hnot⟩ := hcut
  obtain ⟨W0, hW0, h1, h2⟩ := hsu p hp
  have hW0W : W0 = W := by
    by_contra hne
    exact hnot ⟨W0, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_erase.2 ⟨hne, hW0⟩)), h1, h2⟩
  subst hW0W
  set t := s.filter (fun p => p.1 ∈ W0 ∧ p.2 ∈ W0) with ht
  have htb : Bal t := bal_restrict hP (hbal s hs𝒞) hsu hW0
  have htin : ∀ p ∈ t, p.1 ∈ W0 ∧ p.2 ∈ W0 := fun p hp => (Finset.mem_filter.1 hp).2
  have hce := cross_eq t W0 S htin htb
  have hpt : p ∈ t := Finset.mem_filter.2 ⟨hp, h1, h2⟩
  have hpos : 0 < (t.filter (fun p => p.1 ∈ S ∧ p.2 ∈ W0 \ S)).card := by
    by_cases hp1 : p.1 ∈ S
    · have hp2 : p.2 ∉ S := by
        intro hp2
        exact hnot ⟨S, Finset.mem_insert_self _ _, hp1, hp2⟩
      exact Finset.card_pos.2 ⟨p, Finset.mem_filter.2 ⟨hpt, hp1, Finset.mem_sdiff.2 ⟨h2, hp2⟩⟩⟩
    · have hp2 : p.2 ∈ S := by
        by_contra hp2
        exact hnot ⟨W0 \ S, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
          Finset.mem_sdiff.2 ⟨h1, hp1⟩, Finset.mem_sdiff.2 ⟨h2, hp2⟩⟩
      rw [hce]
      exact Finset.card_pos.2 ⟨p, Finset.mem_filter.2 ⟨hpt, Finset.mem_sdiff.2 ⟨h1, hp1⟩, hp2⟩⟩
  obtain ⟨q, hq⟩ := Finset.card_pos.1 hpos
  obtain ⟨hqt, hq1, hq2⟩ := Finset.mem_filter.1 hq
  obtain ⟨hqs, hqW⟩ := Finset.mem_filter.1 hqt
  refine ⟨q, hqs, ?_, hq1, hq2⟩
  exact Finset.mem_biUnion.2 ⟨s, Finset.mem_filter.2 ⟨hs𝒞, hsu⟩, Finset.mem_filter.2 ⟨hqs, hqW⟩⟩

lemma exists_partition (V : Finset α) (𝒞 : Finset (Finset (α × α))) (L lam : ℝ) (hL : 0 ≤ L)
    (hV : ∀ s ∈ 𝒞, ∀ p ∈ s, p.1 ∈ V ∧ p.2 ∈ V) (hbal : ∀ s ∈ 𝒞, Bal s)
    (hcard : ∀ s ∈ 𝒞, (s.card : ℝ) ≤ L)
    (hdisj : (𝒞 : Set (Finset (α × α))).PairwiseDisjoint id) [Fintype α] :
    ∃ P : Finset (Finset α), (∀ W ∈ P, W ⊆ V) ∧ (P : Set (Finset α)).PairwiseDisjoint id ∧
      (cost 𝒞 P : ℝ) ≤ L * lam / 2 * sep V P ∧
      ∀ W ∈ P, ∀ S ⊆ W, lam * S.card * (W \ S).card ≤
        (((keptIn 𝒞 P W).filter (fun p => p.1 ∈ S ∧ p.2 ∈ W \ S)).card : ℝ) := by
  let Inv : Finset (Finset α) → Prop := fun P => (∀ W ∈ P, W ⊆ V) ∧
    (P : Set (Finset α)).PairwiseDisjoint id ∧ (cost 𝒞 P : ℝ) ≤ L * lam / 2 * sep V P
  have h0 : Inv {V} := by
    refine ⟨by simp, by simp, ?_⟩
    have hc : cost 𝒞 {V} = 0 := by
      unfold cost
      rw [Finset.sum_eq_zero]
      intro s hs
      exfalso
      obtain ⟨hs𝒞, hns⟩ := Finset.mem_filter.1 hs
      apply hns
      intro p hp
      exact ⟨V, Finset.mem_singleton_self _, (hV s hs𝒞 p hp).1, (hV s hs𝒞 p hp).2⟩
    simp [hc, sep]
  obtain ⟨P, hPmem, hmax⟩ := Finset.exists_max_image (Finset.univ.filter Inv) Finset.card
    ⟨{V}, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩
  obtain ⟨-, hPsub, hPdisj, hPcost⟩ := Finset.mem_filter.1 hPmem
  refine ⟨P, hPsub, hPdisj, hPcost, ?_⟩
  intro W hW S hSW
  by_contra hlt
  push Not at hlt
  set e := (keptIn 𝒞 P W).filter (fun p => p.1 ∈ S ∧ p.2 ∈ W \ S) with he
  have hecnn : (0 : ℝ) ≤ e.card := Nat.cast_nonneg _
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · exfalso; rw [h] at hlt; simp at hlt; linarith
    · exact h
  have hWSne : (W \ S).Nonempty := by
    rcases (W \ S).eq_empty_or_nonempty with h | h
    · exfalso; rw [h] at hlt; simp at hlt; linarith
    · exact h
  set P' := insert S (insert (W \ S) (P.erase W)) with hP'
  -- disjointness / card facts
  have hS_notin : S ∉ P.erase W := by
    intro h
    obtain ⟨hne, hSP⟩ := Finset.mem_erase.1 h
    have := hPdisj hSP hW hne
    obtain ⟨x, hx⟩ := hSne
    exact Finset.disjoint_left.1 this hx (hSW hx)
  have hWS_notin : W \ S ∉ P.erase W := by
    intro h
    obtain ⟨hne, hSP⟩ := Finset.mem_erase.1 h
    have := hPdisj hSP hW hne
    obtain ⟨x, hx⟩ := hWSne
    exact Finset.disjoint_left.1 this hx (Finset.sdiff_subset hx)
  have hS_ne_WS : S ≠ W \ S := by
    intro h
    obtain ⟨x, hx⟩ := hSne
    have hx' := hx
    rw [h] at hx'
    exact (Finset.mem_sdiff.1 hx').2 hx
  have hcard' : P'.card = P.card + 1 := by
    rw [hP', Finset.card_insert_of_notMem, Finset.card_insert_of_notMem hWS_notin,
      Finset.card_erase_of_mem hW]
    · have : 0 < P.card := Finset.card_pos.2 ⟨W, hW⟩
      omega
    · intro h
      rcases Finset.mem_insert.1 h with h | h
      · exact hS_ne_WS h
      · exact hS_notin h
  have hdisj' : (P' : Set (Finset α)).PairwiseDisjoint id := by
    rw [hP', Finset.coe_insert, Finset.coe_insert]
    have hE : ((P.erase W : Finset (Finset α)) : Set (Finset α)).PairwiseDisjoint id :=
      hPdisj.subset (Finset.coe_subset.2 (Finset.erase_subset _ _))
    refine Set.PairwiseDisjoint.insert (Set.PairwiseDisjoint.insert hE ?_) ?_
    · intro j hj _
      have hj' := Finset.mem_erase.1 (Finset.mem_coe.1 hj)
      exact Disjoint.mono_left Finset.sdiff_subset (hPdisj hW hj'.2 (Ne.symm hj'.1))
    · intro j hj _
      rcases hj with hj | hj
      · subst hj; exact Finset.disjoint_sdiff
      · have hj' := Finset.mem_erase.1 (Finset.mem_coe.1 hj)
        exact Disjoint.mono_left hSW (hPdisj hW hj'.2 (Ne.symm hj'.1))
  have hsub' : ∀ W' ∈ P', W' ⊆ V := by
    intro W' hW'
    rcases Finset.mem_insert.1 hW' with h | h
    · subst h; exact hSW.trans (hPsub W hW)
    rcases Finset.mem_insert.1 h with h | h
    · subst h; exact Finset.sdiff_subset.trans (hPsub W hW)
    · exact hPsub W' (Finset.mem_of_mem_erase h)
  -- separation
  have hsep : sep V P' = sep V P + 2 * S.card * (W \ S).card := by
    have hc := Finset.card_sdiff_add_card_eq_card hSW
    have hcR : ((W \ S).card : ℝ) = W.card - S.card := by
      have : ((W \ S).card : ℝ) + S.card = W.card := by exact_mod_cast hc
      linarith
    unfold sep
    rw [hP', Finset.sum_insert, Finset.sum_insert hWS_notin, ← Finset.add_sum_erase P _ hW]
    · rw [hcR]; ring
    · intro h
      rcases Finset.mem_insert.1 h with h | h
      · exact hS_ne_WS h
      · exact hS_notin h
  -- cost
  set Nw := 𝒞.filter (fun s => ¬ Uncut P' s ∧ Uncut P s) with hNw
  have hcost1 : cost 𝒞 P' ≤ cost 𝒞 P + ∑ s ∈ Nw, s.card := by
    unfold cost
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s _
    by_cases h1 : Uncut P' s <;> by_cases h2 : Uncut P s <;> simp [h1, h2]
  have hNwcard : Nw.card ≤ e.card := by
    let g : (α × α) → Finset (α × α) := fun p =>
      if h : ∃ s ∈ 𝒞, p ∈ s then Classical.choose h else ∅
    have hsub : Nw ⊆ e.image g := by
      intro s hs
      obtain ⟨hs𝒞, hcut, hu⟩ := Finset.mem_filter.1 hs
      obtain ⟨q, hqs, hqk, hq1, hq2⟩ := exists_cross_arc hPdisj hbal hW hs𝒞 hu hcut
      refine Finset.mem_image.2 ⟨q, Finset.mem_filter.2 ⟨hqk, hq1, hq2⟩, ?_⟩
      have hex : ∃ s ∈ 𝒞, q ∈ s := ⟨s, hs𝒞, hqs⟩
      simp only [g, dif_pos hex]
      obtain ⟨hc𝒞, hcq⟩ := Classical.choose_spec hex
      by_contra hne
      exact Finset.disjoint_left.1 (hdisj hc𝒞 hs𝒞 hne) hcq hqs
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have hNwsum : (∑ s ∈ Nw, (s.card : ℝ)) ≤ L * Nw.card := by
    calc (∑ s ∈ Nw, (s.card : ℝ)) ≤ ∑ s ∈ Nw, L :=
          Finset.sum_le_sum (fun s hs => hcard s (Finset.mem_filter.1 hs).1)
      _ = L * Nw.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hInv' : Inv P' := by
    refine ⟨hsub', hdisj', ?_⟩
    have h1 : (cost 𝒞 P' : ℝ) ≤ cost 𝒞 P + ∑ s ∈ Nw, (s.card : ℝ) := by
      exact_mod_cast hcost1
    have h2 : (Nw.card : ℝ) ≤ e.card := by exact_mod_cast hNwcard
    rw [hsep]
    have h3 : L * (Nw.card : ℝ) ≤ L * (lam * S.card * (W \ S).card) :=
      mul_le_mul_of_nonneg_left (h2.trans hlt.le) hL
    nlinarith
  have := hmax P' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hInv'⟩)
  omega

lemma card_filter_perm {ι : Type} [Fintype ι] (σ : Equiv.Perm ι) (P : ι → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun i => P (σ i))).card = (Finset.univ.filter P).card :=
  Finset.card_equiv σ (by intro i; simp)

lemma cycle_bal {l : ℕ} (w : Fin l → α) (hinj : Function.Injective w) :
    Bal (Finset.univ.image (fun i : Fin l => (w i, w (finRotate l i)))) := by
  have hf : Function.Injective (fun i : Fin l => (w i, w (finRotate l i))) := by
    intro i j h
    exact hinj (Prod.ext_iff.1 h).1
  intro x
  unfold outC inC
  rw [Finset.filter_image, Finset.filter_image, Finset.card_image_of_injective _ hf,
    Finset.card_image_of_injective _ hf]
  exact (card_filter_perm (finRotate l) (fun i => w i = x)).symm

lemma exists_family [Fintype α] (V : Finset α) (R : α → α → Prop) [DecidableRel R] (N : ℕ)
    (θ : ℝ) (hθ : 0 < θ) (hV0 : V.Nonempty) (hV : V.card ≤ N)
    (hdeg : ∀ x ∈ V, θ * N ≤ ((V.filter (fun y => R x y)).card : ℝ)) (hbig : 16 < θ ^ 2 * N) :
    ∃ 𝒞 : Finset (Finset (α × α)),
      (∀ s ∈ 𝒞, s ⊆ (V ×ˢ V).filter (fun p => R p.1 p.2) ∧ Bal s ∧ (s.card : ℝ) ≤ 8 / θ) ∧
      (𝒞 : Set (Finset (α × α))).PairwiseDisjoint id ∧
      (θ * N) ^ 2 / 8 ≤ ((𝒞.biUnion id).card : ℝ) := by
  set A := (V ×ˢ V).filter (fun p => R p.1 p.2) with hA
  let IsFam : Finset (Finset (α × α)) → Prop := fun 𝒞 =>
    (∀ s ∈ 𝒞, s ⊆ A ∧ Bal s ∧ (s.card : ℝ) ≤ 8 / θ) ∧
      (𝒞 : Set (Finset (α × α))).PairwiseDisjoint id
  obtain ⟨𝒞, h𝒞mem, hmax⟩ := Finset.exists_max_image (Finset.univ.filter IsFam)
    (fun 𝒞 => (𝒞.biUnion id).card)
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [IsFam]⟩⟩
  obtain ⟨-, hgood, hdisj⟩ := Finset.mem_filter.1 h𝒞mem
  refine ⟨𝒞, hgood, hdisj, ?_⟩
  by_contra hlt
  push Not at hlt
  set Y := 𝒞.biUnion id with hY
  set d : ℝ := θ * N with hd
  have hN : (0 : ℝ) < N := by
    by_contra h
    push Not at h
    nlinarith [sq_nonneg θ]
  have hdpos : 0 < d := mul_pos hθ hN
  obtain ⟨x0, hx0⟩ := hV0
  have hVd : d ≤ V.card := (hdeg x0 hx0).trans (by exact_mod_cast Finset.card_filter_le _ _)
  set B := V.filter (fun x => d / 2 < (outC Y x : ℝ)) with hB
  have hBcard : (B.card : ℝ) < d / 4 := by
    have h1 : (B.card : ℝ) * (d / 2) ≤ Y.card := by
      calc (B.card : ℝ) * (d / 2) = ∑ x ∈ B, d / 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ B, (outC Y x : ℝ) :=
            Finset.sum_le_sum (fun x hx => le_of_lt (Finset.mem_filter.1 hx).2)
        _ = ((∑ x ∈ B, outC Y x : ℕ) : ℝ) := by push_cast; rfl
        _ = ((Y.filter (fun p => p.1 ∈ B)).card : ℝ) := by rw [sum_outC]
        _ ≤ Y.card := by exact_mod_cast Finset.card_filter_le _ _
    by_contra h
    push Not at h
    nlinarith
  set G := V \ B with hG
  let R' : α → α → Prop := fun x y => R x y ∧ (x, y) ∉ Y
  have hdegG : ∀ x ∈ G, d / 4 < ((G.filter (fun y => R' x y)).card : ℝ) := by
    intro x hx
    obtain ⟨hxV, hxB⟩ := Finset.mem_sdiff.1 hx
    have hout : (outC Y x : ℝ) ≤ d / 2 := by
      by_contra h
      push Not at h
      exact hxB (Finset.mem_filter.2 ⟨hxV, h⟩)
    have hsub : V.filter (fun y => R x y) ⊆
        G.filter (fun y => R' x y) ∪ (V.filter (fun y => (x, y) ∈ Y) ∪ B) := by
      intro y hy
      obtain ⟨hyV, hR⟩ := Finset.mem_filter.1 hy
      by_cases hyY : (x, y) ∈ Y
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hyV, hyY⟩))
      by_cases hyB : y ∈ B
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hyB)
      · exact Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hyV, hyB⟩, hR, hyY⟩)
    have hc1 := (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _))
    have hc2 : (V.filter (fun y => (x, y) ∈ Y)).card ≤ outC Y x := by
      unfold outC
      apply Finset.card_le_card_of_injOn (fun y => (x, y))
      · intro y hy
        have := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
        exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨this, rfl⟩)
      · intro a _ b _ h
        exact (Prod.ext_iff.1 h).2
    have hdx := hdeg x hxV
    have hc1' : ((V.filter (fun y => R x y)).card : ℝ) ≤
        (G.filter (fun y => R' x y)).card + (V.filter (fun y => (x, y) ∈ Y)).card + B.card := by
      have := hc1
      push_cast [← add_assoc] at this ⊢
      exact_mod_cast this
    have hc2' : ((V.filter (fun y => (x, y) ∈ Y)).card : ℝ) ≤ outC Y x := by exact_mod_cast hc2
    linarith
  set r : ℕ := ⌈d / 4⌉₊ with hr
  have hrpos : 0 < r := Nat.ceil_pos.2 (by linarith)
  have hGne : G.Nonempty := by
    have h1 : V.card ≤ G.card + B.card := Finset.card_le_card_sdiff_add_card
    have h1' : (V.card : ℝ) ≤ G.card + B.card := by exact_mod_cast h1
    have : (0 : ℝ) < G.card := by linarith
    exact Finset.card_pos.1 (by exact_mod_cast this)
  have hdegr : ∀ x ∈ G, r ≤ (G.filter (fun y => R' x y)).card :=
    fun x hx => Nat.ceil_le.2 (hdegG x hx).le
  obtain ⟨l, w, hl, hlen, hinj, hmem, harc⟩ := chvatal_szemeredi R' G r hrpos hGne hdegr
  set s := Finset.univ.image (fun i : Fin l => (w i, w (finRotate l i))) with hs
  have hf : Function.Injective (fun i : Fin l => (w i, w (finRotate l i))) := by
    intro i j h
    exact hinj (Prod.ext_iff.1 h).1
  have hscard : s.card = l := by
    rw [hs, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have hGN : (G.card : ℝ) ≤ N := by
    have : G.card ≤ V.card := Finset.card_le_card Finset.sdiff_subset
    exact_mod_cast this.trans hV
  have hlθ : (l : ℝ) ≤ 8 / θ := by
    have hr' : d / 4 ≤ (r : ℝ) := Nat.le_ceil _
    have h1 : (l : ℝ) * (d / 4) ≤ l * (r + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    rw [le_div_iff₀ hθ]
    have : (l : ℝ) * θ * N ≤ 8 * N := by rw [hd] at h1; nlinarith
    nlinarith
  have hsA : s ⊆ A := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    have h1 := (Finset.mem_sdiff.1 (hmem i)).1
    have h2 := (Finset.mem_sdiff.1 (hmem (finRotate l i))).1
    exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h1, h2⟩, (harc i).1⟩
  have hsY : Disjoint s Y := by
    rw [Finset.disjoint_left]
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    exact (harc i).2
  have hsne : s.Nonempty := ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, hl⟩)⟩
  have hfam : IsFam (insert s 𝒞) := by
    refine ⟨?_, ?_⟩
    · intro t ht
      rcases Finset.mem_insert.1 ht with h | h
      · subst h
        exact ⟨hsA, cycle_bal w hinj, by rw [hscard]; exact hlθ⟩
      · exact hgood t h
    · rw [Finset.coe_insert]
      refine hdisj.insert ?_
      intro j hj _
      exact Disjoint.mono_right (Finset.subset_biUnion_of_mem id hj) hsY
  have := hmax (insert s 𝒞) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hfam⟩)
  rw [Finset.biUnion_insert] at this
  simp only [id] at this
  rw [Finset.card_union_of_disjoint hsY] at this
  have := Finset.card_pos.2 hsne
  omega

end

end T4aux

end BinaryThreeLCC.JM

open BinaryThreeLCC.JM BinaryThreeLCC.JM.T4aux

open T4aux in
/-- T4: Lemma 4.2 (variant): an Eulerian cut-dense piece. -/
theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (V : Finset α) (R : α → α → Prop) [DecidableRel R] (N : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (hV0 : V.Nonempty) (hV : V.card ≤ N)
    (hdeg : ∀ x ∈ V, θ * N ≤ ((V.filter (fun y => R x y)).card : ℝ)) :
    ∃ (U : Finset α) (F : Finset (α × α)), U ⊆ V ∧ U.Nonempty ∧
      θ ^ 2 * N / 16 ≤ (U.card : ℝ) ∧
      (∀ p ∈ F, R p.1 p.2 ∧ p.1 ∈ U ∧ p.2 ∈ U) ∧
      (∀ x, (F.filter (fun p => p.1 = x)).card = (F.filter (fun p => p.2 = x)).card) ∧
      ∀ S ⊆ U, θ ^ 3 / 64 * S.card * (U \ S).card ≤
        ((F.filter (fun p => p.1 ∈ S ∧ p.2 ∈ U \ S)).card : ℝ) := by
  classical
  by_cases hsmall : θ ^ 2 * N ≤ 16
  · obtain ⟨x, hx⟩ := hV0
    refine ⟨{x}, ∅, Finset.singleton_subset_iff.2 hx, Finset.singleton_nonempty x, ?_,
      by simp, by simp, ?_⟩
    · rw [Finset.card_singleton]; push_cast; linarith
    · intro S hS
      rcases Finset.subset_singleton_iff.1 hS with h | h
      · subst h; simp
      · subst h; simp
  push Not at hsmall
  have hN : (0 : ℝ) < N := by
    by_contra h
    push Not at h
    nlinarith [sq_nonneg θ]
  obtain ⟨𝒞, hgood, hdisj, hbig⟩ := exists_family V R N θ hθ hV0 hV hdeg hsmall
  have hVarc : ∀ s ∈ 𝒞, ∀ p ∈ s, p.1 ∈ V ∧ p.2 ∈ V := by
    intro s hs p hp
    have := (Finset.mem_product.1 (Finset.mem_filter.1 ((hgood s hs).1 hp)).1)
    exact this
  obtain ⟨P, hPsub, hPdisj, hcost, hcutd⟩ := exists_partition V 𝒞 (8 / θ) (θ ^ 3 / 64)
    (by positivity) hVarc (fun s hs => (hgood s hs).2.1) (fun s hs => (hgood s hs).2.2) hdisj
  -- totals
  set K : ℕ := ∑ s ∈ 𝒞.filter (Uncut P), s.card with hK
  have htot : (𝒞.biUnion id).card = ∑ s ∈ 𝒞, s.card := Finset.card_biUnion hdisj
  have hsplit : K + cost 𝒞 P = ∑ s ∈ 𝒞, s.card := by
    rw [hK, cost]; exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hsumW : ∑ W ∈ P, W.card ≤ V.card := by
    have hb := Finset.card_biUnion hPdisj
    simp only [id] at hb
    rw [← hb]
    apply Finset.card_le_card
    intro y hy
    obtain ⟨W, hW, hyW⟩ := Finset.mem_biUnion.1 hy
    exact hPsub W hW hyW
  have hsumWR : (∑ W ∈ P, (W.card : ℝ)) ≤ N := by
    have : ∑ W ∈ P, W.card ≤ N := hsumW.trans hV
    exact_mod_cast this
  have hsep : sep V P ≤ (N : ℝ) ^ 2 := by
    unfold sep
    have hVN : (V.card : ℝ) ≤ N := by exact_mod_cast hV
    calc ∑ W ∈ P, (W.card : ℝ) * (V.card - W.card) ≤ ∑ W ∈ P, (W.card : ℝ) * N := by
          apply Finset.sum_le_sum
          intro W _
          have : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
          nlinarith
      _ = (∑ W ∈ P, (W.card : ℝ)) * N := by rw [Finset.sum_mul]
      _ ≤ (N : ℝ) * N := mul_le_mul_of_nonneg_right hsumWR (Nat.cast_nonneg _)
      _ = (N : ℝ) ^ 2 := by ring
  have hcostR : (cost 𝒞 P : ℝ) ≤ θ ^ 2 * N ^ 2 / 16 := by
    have hc : 8 / θ * (θ ^ 3 / 64) / 2 = θ ^ 2 / 16 := by field_simp; ring
    rw [hc] at hcost
    have : θ ^ 2 / 16 * sep V P ≤ θ ^ 2 / 16 * (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsep (by positivity)
    linarith
  have hKR : θ ^ 2 * N ^ 2 / 16 ≤ (K : ℝ) := by
    have h1 : (K : ℝ) + cost 𝒞 P = ((𝒞.biUnion id).card : ℝ) := by
      rw [htot]; exact_mod_cast hsplit
    nlinarith
  -- sum over blocks of kept arcs
  have hkept : K ≤ ∑ W ∈ P, (keptIn 𝒞 P W).card := by
    have hdisjU : ((𝒞.filter (Uncut P) : Finset (Finset (α × α))) : Set (Finset (α × α))).PairwiseDisjoint id :=
      hdisj.subset (Finset.coe_subset.2 (Finset.filter_subset _ _))
    have hKc : K = ((𝒞.filter (Uncut P)).biUnion id).card := by
      rw [Finset.card_biUnion hdisjU]; rfl
    rw [hKc]
    refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
    intro p hp
    obtain ⟨s, hs, hps⟩ := Finset.mem_biUnion.1 hp
    obtain ⟨hs𝒞, hu⟩ := Finset.mem_filter.1 hs
    obtain ⟨W, hW, h1, h2⟩ := hu p hps
    exact Finset.mem_biUnion.2 ⟨W, hW, Finset.mem_biUnion.2
      ⟨s, hs, Finset.mem_filter.2 ⟨hps, h1, h2⟩⟩⟩
  set c : ℝ := θ ^ 2 * N / 16 with hc
  have hgoodW : ∃ W ∈ P, 0 < (keptIn 𝒞 P W).card ∧ c * W.card ≤ (keptIn 𝒞 P W).card := by
    by_contra hno
    push Not at hno
    have hle : ∀ W ∈ P, ((keptIn 𝒞 P W).card : ℝ) ≤ c * W.card := by
      intro W hW
      rcases Nat.eq_zero_or_pos (keptIn 𝒞 P W).card with h | h
      · rw [h]; push_cast; positivity
      · exact (hno W hW h).le
    have hKpos : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) hKR
    have hex : ∃ W ∈ P, 0 < (keptIn 𝒞 P W).card := by
      by_contra h
      push Not at h
      have : ∑ W ∈ P, (keptIn 𝒞 P W).card = 0 :=
        Finset.sum_eq_zero (fun W hW => Nat.le_zero.1 (h W hW))
      have : (K : ℝ) ≤ 0 := by exact_mod_cast (hkept.trans this.le)
      linarith
    obtain ⟨W0, hW0, hpos0⟩ := hex
    have hlt : ∑ W ∈ P, ((keptIn 𝒞 P W).card : ℝ) < ∑ W ∈ P, c * W.card :=
      Finset.sum_lt_sum hle ⟨W0, hW0, hno W0 hW0 hpos0⟩
    have hk' : (K : ℝ) ≤ ∑ W ∈ P, ((keptIn 𝒞 P W).card : ℝ) := by exact_mod_cast hkept
    have hc' : ∑ W ∈ P, c * (W.card : ℝ) ≤ c * N := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hsumWR (by positivity)
    have : c * N = θ ^ 2 * N ^ 2 / 16 := by rw [hc]; ring
    linarith
  obtain ⟨W, hW, hkpos, hkc⟩ := hgoodW
  have hksq : (keptIn 𝒞 P W).card ≤ W.card * W.card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨s, -, hps⟩ := Finset.mem_biUnion.1 hp
    exact Finset.mem_product.2 (Finset.mem_filter.1 hps).2
  have hWpos : 0 < W.card := by
    rcases Nat.eq_zero_or_pos W.card with h | h
    · rw [h] at hksq; omega
    · exact h
  refine ⟨W, keptIn 𝒞 P W, hPsub W hW, Finset.card_pos.1 hWpos, ?_, ?_, ?_, ?_⟩
  · have h1 : c * W.card ≤ (W.card : ℝ) * W.card :=
      hkc.trans (by exact_mod_cast hksq)
    have h2 : (0 : ℝ) < W.card := by exact_mod_cast hWpos
    have : c ≤ W.card := le_of_mul_le_mul_right h1 h2
    rw [hc] at this
    exact this
  · intro p hp
    obtain ⟨s, hs, hps⟩ := Finset.mem_biUnion.1 hp
    obtain ⟨hpS, h1, h2⟩ := Finset.mem_filter.1 hps
    have hA := (hgood s (Finset.mem_filter.1 hs).1).1 hpS
    exact ⟨(Finset.mem_filter.1 hA).2, h1, h2⟩
  · have hb : Bal (keptIn 𝒞 P W) := by
      unfold keptIn
      apply bal_biUnion
      · intro i hi j hj hij
        exact Finset.disjoint_filter_filter
          (hdisj (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).1
            (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).1 hij)
      · intro s hs
        obtain ⟨hs𝒞, hu⟩ := Finset.mem_filter.1 hs
        exact bal_restrict hPdisj (hgood s hs𝒞).2.1 hu hW
    exact hb
  · exact hcutd W hW


namespace BinaryThreeLCC.JM

end BinaryThreeLCC.JM

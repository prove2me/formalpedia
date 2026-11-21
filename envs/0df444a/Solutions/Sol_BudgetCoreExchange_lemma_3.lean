-- Prove2me | solution 1 for BudgetCoreExchange.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:52:29.538565+00:00
-- url     : https://prove2.me/submissions/36f06b74-15c6-4a9c-9388-5ad11b84c821

import Mathlib
import Definitions.Def_BudgetCoreExchange_Exchange
import Definitions.Def_BudgetCoreExchange_InCore
import Definitions.Def_BudgetCoreExchange_QSAT2
import Definitions.Def_BudgetCoreExchange_gadget
namespace Aux_BCE1

open BudgetCoreExchange BudgetCoreExchange.Gadget

lemma xor_le {Item : Type} [DecidableEq Item] (bs : List (Finset Item × ℝ)) (S : Finset Item)
    (C : ℝ) (hC : 0 ≤ C) (h : ∀ b ∈ bs, b.1 ⊆ S → b.2 ≤ C) : (xorBid bs).value S ≤ C := by
  unfold xorBid Bid.value
  induction bs with
  | nil => simpa using hC
  | cons b t ih =>
    simp only [List.map_cons, List.foldr_cons]
    apply max_le
    · unfold BidGroup.value
      split_ifs with h1
      · have e : (([b].filter fun p => decide (p.1 ⊆ S)).map fun p => p.2).sum = b.2 := by
          simp [h1]
        simp only at e ⊢
        rw [e]
        exact h b List.mem_cons_self h1
      · exact hC
    · exact ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))

lemma parts_le {α Item : Type} [DecidableEq Item] (F : α → Finset Item) (S : Finset Item)
    (c : α → Bool) (l0 : List α) :
    ((((l0.filter c).map fun l => (F l, (1 : ℝ))).filter fun p => decide (p.1 ⊆ S)).map
      fun p => p.2).sum ≤ (l0.map fun l => if F l ⊆ S then (1 : ℝ) else 0).sum := by
  induction l0 with
  | nil => simp
  | cons a t ih =>
    by_cases hc : c a = true
    · by_cases hs : F a ⊆ S
      · simp only [List.filter_cons, hc, if_true, List.map_cons, hs, decide_true,
          List.sum_cons]
        linarith
      · simp only [List.filter_cons, hc, if_true, List.map_cons, hs, decide_false,
          List.sum_cons, Bool.false_eq_true, if_false]
        linarith
    · have hc' : c a = false := by simpa using hc
      simp only [List.filter_cons, hc', List.map_cons, List.sum_cons, Bool.false_eq_true,
        if_false]
      have : (0 : ℝ) ≤ if F a ⊆ S then 1 else 0 := by split_ifs <;> norm_num
      linarith

lemma sum_BKind (F : BKind → ℝ) :
    ∑ k, F k = F BKind.K + F BKind.M + F BKind.chi1 + F BKind.chi2 + F BKind.lam1 +
      F BKind.lam2 := by
  show ∑ k ∈ ({BKind.K, BKind.M, BKind.chi1, BKind.chi2, BKind.lam1, BKind.lam2} :
    Finset BKind), F k = _
  simp [Finset.sum_insert]
  ring

theorem main (ϕ : DNF) (T U V W : ℝ) (hA : Admissible ϕ T U V W)
    (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (ho : IsNWEquilibrium ϕ T U V W o)
    (i : Fin ϕ.n) :
    ∃ l : Fin ϕ.numTerms,
      Gadget.Kb l i ⊆ o.S (Gadget.BK i) ∨ Gadget.Kbar l i ⊆ o.S (Gadget.BK i) := by
  obtain ⟨hT0, hT1, hU, hV, hW⟩ := hA
  obtain ⟨⟨hfeas, _⟩, hwel⟩ := ho
  have hn1 : (1 : ℝ) ≤ ϕ.n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Fin.pos i).ne'
  have hL0 : (0 : ℝ) ≤ ϕ.numTerms := Nat.cast_nonneg _
  have hU0 : 0 < U := by nlinarith
  have hV0 : 0 < V := by linarith
  have hLV : (ϕ.numTerms : ℝ) < V := by nlinarith
  have hW0 : 0 < W := by nlinarith
  by_contra hno
  push_neg at hno
  set E := gadget ϕ T U V W with hE
  -- seller values vanish
  have hsval : ∀ s Z, E.sval s Z = 0 := by
    intro s Z; simp [Exchange.sval, hE, gadget, Bid.value]
  -- buyer bounds
  have hK : ∀ i' S, E.bval (BK i') S ≤ W := by
    intro i' S
    unfold Exchange.bval
    refine xor_le _ S W hW0.le ?_
    intro b hb _
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
      List.not_mem_nil, or_false] at hb
    obtain ⟨l, hl | hl⟩ := hb <;> rw [hl]
  have hKi : E.bval (BK i) (o.S (BK i)) ≤ 0 := by
    unfold Exchange.bval
    refine xor_le _ _ 0 le_rfl ?_
    intro b hb hsub
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
      List.not_mem_nil, or_false] at hb
    obtain ⟨l, hl | hl⟩ := hb
    · rw [hl] at hsub; exact absurd hsub (hno l).1
    · rw [hl] at hsub; exact absurd hsub (hno l).2
  have hM : ∀ i' S, E.bval (Sum.inl (BKind.M, i')) S ≤ 2 * V := by
    intro i' S
    unfold Exchange.bval
    refine xor_le _ S _ (by linarith) ?_
    intro b hb _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | hb <;> rw [hb]
  have hc1 : ∀ i' S, E.bval (Sum.inl (BKind.chi1, i')) S ≤ V := by
    intro i' S
    unfold Exchange.bval
    refine xor_le _ S _ hV0.le ?_
    intro b hb _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | hb <;> rw [hb]
  have hc2 : ∀ i' S, E.bval (Sum.inl (BKind.chi2, i')) S ≤ V := by
    intro i' S
    unfold Exchange.bval
    refine xor_le _ S _ hV0.le ?_
    intro b hb _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | hb <;> rw [hb]
  have hl1 : ∀ i' S, E.bval (Sum.inl (BKind.lam1, i')) S ≤ V := by
    intro i' S
    unfold Exchange.bval
    refine xor_le _ S _ hV0.le ?_
    intro b hb _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | hb <;> rw [hb] <;> dsimp only <;> linarith
  have hl2 : ∀ i' S, E.bval (Sum.inl (BKind.lam2, i')) S ≤ V := by
    intro i' S
    unfold Exchange.bval
    refine xor_le _ S _ hV0.le ?_
    intro b hb _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | hb <;> rw [hb] <;> dsimp only <;> linarith
  -- the G-buyers
  have hG : ∀ j S, E.bval (BG j) S ≤
      ∑ l : Fin ϕ.numTerms, if Fpf l ⊆ S then (1 : ℝ) else 0 := by
    intro j S
    have hcnt0 : (0 : ℝ) ≤ ∑ l : Fin ϕ.numTerms, if Fpf l ⊆ S then (1 : ℝ) else 0 :=
      Finset.sum_nonneg (fun l _ => by split_ifs <;> norm_num)
    have hgrp : ∀ (g : Finset (GItem ϕ)) (c : Fin ϕ.numTerms → Bool),
        (BidGroup.value ⟨g, ((List.finRange ϕ.numTerms).filter c).map
          fun l => (Fpf l, (1 : ℝ))⟩ S) ≤
        ∑ l : Fin ϕ.numTerms, if Fpf l ⊆ S then (1 : ℝ) else 0 := by
      intro g c
      unfold BidGroup.value
      split_ifs
      · rw [Fin.sum_univ_def]
        exact parts_le Fpf S c _
      · exact hcnt0
    unfold Exchange.bval Bid.value
    show max _ (max _ 0) ≤ _
    exact max_le (hgrp _ _) (max_le (hgrp _ _) hcnt0)
  -- supply of the ψ items
  have hsupply : ∀ l : Fin ϕ.numTerms,
      ∑ j : Fin ϕ.m, (if Fpf l ⊆ o.S (BG j) then (1 : ℝ) else 0) ≤ 1 := by
    intro l
    have hk : ∀ S : Finset (GItem ϕ), Fpf l ⊆ S → psi l i i ∈ S := by
      intro S hS; apply hS
      unfold Fpf Tpsi
      exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨(i, i), Finset.mem_univ _, rfl⟩)
    have hfe := hfeas.2.2.2 (psi l i i)
    have hsell : ((Coalition.grand (GBuyer ϕ) (GSeller ϕ)).sellers.filter
        fun s => psi l i i ∈ o.Z s).card ≤ 1 := by
      apply Finset.card_le_one.2
      intro a ha b hb
      have hza := (Finset.mem_filter.1 ha).2
      have hzb := (Finset.mem_filter.1 hb).2
      have h1 : ∀ s, psi l i i ∈ o.Z s → s = Sum.inr (Sum.inl l) := by
        intro s hs
        have hend := (hfeas.2.1 s (Finset.mem_univ _)).1 hs
        rcases s with i' | l' | u | u
        · simp [hE, gadget, psi, chi, chiBar] at hend
        · simp [hE, gadget, Tpsi, psi] at hend
          first | rw [hend] | rw [hend.1] | (subst hend; rfl)
        · simp [hE, gadget, psi, gam, gamBar, phi] at hend
        · simp [hE, gadget, psi, lam, lamBar] at hend
      rw [h1 a hza, h1 b hzb]
    have hbuy : (Finset.univ.filter fun j : Fin ϕ.m => Fpf l ⊆ o.S (BG j)).card ≤
        ((Coalition.grand (GBuyer ϕ) (GSeller ϕ)).buyers.filter
          fun b => psi l i i ∈ o.S b).card := by
      apply Finset.card_le_card_of_injOn (fun j => (Sum.inr j : GBuyer ϕ))
      · intro j hj
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hk _ (Finset.mem_filter.1 hj).2⟩
      · intro a _ b _ h
        exact Sum.inr_injective h
    have : (Finset.univ.filter fun j : Fin ϕ.m => Fpf l ⊆ o.S (BG j)).card ≤ 1 := by omega
    rw [Finset.sum_boole]
    exact_mod_cast this
  have hGsum : ∑ j : Fin ϕ.m, E.bval (BG j) (o.S (BG j)) ≤ ϕ.numTerms := by
    calc ∑ j : Fin ϕ.m, E.bval (BG j) (o.S (BG j))
        ≤ ∑ j : Fin ϕ.m, ∑ l : Fin ϕ.numTerms, if Fpf l ⊆ o.S (BG j) then (1 : ℝ) else 0 :=
          Finset.sum_le_sum (fun j _ => hG j _)
      _ = ∑ l : Fin ϕ.numTerms, ∑ j : Fin ϕ.m, if Fpf l ⊆ o.S (BG j) then (1 : ℝ) else 0 :=
          Finset.sum_comm
      _ ≤ ∑ l : Fin ϕ.numTerms, (1 : ℝ) := Finset.sum_le_sum (fun l _ => hsupply l)
      _ = ϕ.numTerms := by simp
  -- the K-buyers
  have hKsum : ∑ i' : Fin ϕ.n, E.bval (BK i') (o.S (BK i')) ≤ ((ϕ.n : ℝ) - 1) * W := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have h1 : ∑ i' ∈ Finset.univ.erase i, E.bval (BK i') (o.S (BK i')) ≤
        ∑ i' ∈ Finset.univ.erase i, W := Finset.sum_le_sum (fun i' _ => hK i' _)
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h1
    have h2 : ((ϕ.n - 1 : ℕ) : ℝ) = (ϕ.n : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (Fin.pos i).ne')]; simp
    rw [h2] at h1
    linarith
  -- welfare bound
  have hwelf : welfare E o ≤ ((ϕ.n : ℝ) - 1) * W + 6 * ϕ.n * V + ϕ.numTerms := by
    unfold welfare
    simp only [hsval, Finset.sum_const_zero, sub_zero]
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [sum_BKind]
    have hKsum' : ∑ i' : Fin ϕ.n, E.bval (Sum.inl (BKind.K, i')) (o.S (Sum.inl (BKind.K, i'))) ≤
        ((ϕ.n : ℝ) - 1) * W := hKsum
    have hb : ∀ i' : Fin ϕ.n,
        E.bval (Sum.inl (BKind.M, i')) (o.S (Sum.inl (BKind.M, i'))) +
        E.bval (Sum.inl (BKind.chi1, i')) (o.S (Sum.inl (BKind.chi1, i'))) +
        E.bval (Sum.inl (BKind.chi2, i')) (o.S (Sum.inl (BKind.chi2, i'))) +
        E.bval (Sum.inl (BKind.lam1, i')) (o.S (Sum.inl (BKind.lam1, i'))) +
        E.bval (Sum.inl (BKind.lam2, i')) (o.S (Sum.inl (BKind.lam2, i'))) ≤ 6 * V := by
      intro i'
      have := hM i' (o.S (Sum.inl (BKind.M, i')))
      have := hc1 i' (o.S (Sum.inl (BKind.chi1, i')))
      have := hc2 i' (o.S (Sum.inl (BKind.chi2, i')))
      have := hl1 i' (o.S (Sum.inl (BKind.lam1, i')))
      have := hl2 i' (o.S (Sum.inl (BKind.lam2, i')))
      linarith
    have hsum6 := Finset.sum_le_sum (fun i' (_ : i' ∈ (Finset.univ : Finset (Fin ϕ.n))) => hb i')
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsum6
    have hGs : ∑ j : Fin ϕ.m, E.bval (Sum.inr j) (o.S (Sum.inr j)) ≤ ϕ.numTerms := hGsum
    linarith
  have : ((ϕ.n : ℝ) - 1) * W + 6 * ϕ.n * V + ϕ.numTerms < ϕ.n * W := by nlinarith
  linarith

end Aux_BCE1

namespace Aux_BCE

open BudgetCoreExchange BudgetCoreExchange.Gadget

/-! ### Generic lemmas on bids -/

lemma grp_val {Item : Type} [DecidableEq Item] (B : Finset Item) (w : ℝ) (S : Finset Item) :
    BidGroup.value ⟨B, [(B, w)]⟩ S = if B ⊆ S then w else 0 := by
  unfold BidGroup.value
  by_cases h : B ⊆ S
  · simp [h]
  · simp [h]

lemma xor_val {Item : Type} [DecidableEq Item] (bs : List (Finset Item × ℝ)) (S : Finset Item) :
    (xorBid bs).value S = (bs.map fun b => if b.1 ⊆ S then b.2 else 0).foldr max 0 := by
  unfold xorBid Bid.value
  rw [List.map_map]
  exact congrArg (List.foldr max 0) (List.map_congr_left fun b _ => grp_val b.1 b.2 S)

lemma xor_ge {Item : Type} [DecidableEq Item] (bs : List (Finset Item × ℝ)) (S : Finset Item)
    (b : Finset Item × ℝ) (hb : b ∈ bs) (hS : b.1 ⊆ S) : b.2 ≤ (xorBid bs).value S := by
  rw [xor_val]
  induction bs with
  | nil => simp at hb
  | cons a t ih =>
    rw [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 hb with h | h
    · subst h
      rw [if_pos hS]
      exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma xor_nonneg {Item : Type} [DecidableEq Item] (bs : List (Finset Item × ℝ))
    (S : Finset Item) : 0 ≤ (xorBid bs).value S := by
  rw [xor_val]
  induction bs with
  | nil => exact le_refl _
  | cons a t ih =>
    rw [List.map_cons, List.foldr_cons]
    exact le_trans ih (le_max_right _ _)

lemma xor2 {Item : Type} [DecidableEq Item] (B1 B2 : Finset Item) (w1 w2 : ℝ)
    (S : Finset Item) :
    (xorBid [(B1, w1), (B2, w2)]).value S =
      max (if B1 ⊆ S then w1 else 0) (max (if B2 ⊆ S then w2 else 0) 0) :=
  (xor_val [(B1, w1), (B2, w2)] S).trans rfl

lemma xor_sdiff {Item : Type} [DecidableEq Item] (bs : List (Finset Item × ℝ))
    (S N : Finset Item) (h : ∀ b ∈ bs, Disjoint b.1 N) :
    (xorBid bs).value (S \ N) = (xorBid bs).value S := by
  rw [xor_val, xor_val]
  refine congrArg (List.foldr max 0) (List.map_congr_left fun b hb => ?_)
  show (if b.1 ⊆ S \ N then b.2 else 0) = (if b.1 ⊆ S then b.2 else 0)
  have e : b.1 ⊆ S \ N ↔ b.1 ⊆ S := by
    rw [Finset.subset_sdiff]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', h b hb⟩⟩
  by_cases h1 : b.1 ⊆ S
  · rw [if_pos h1, if_pos (e.2 h1)]
  · rw [if_neg h1, if_neg (fun h' => h1 (e.1 h'))]

/-- The core inequality: in a core outcome no reallocation of the goods of a seller set
`Ts` lets the buyers pay more than the current receipts of `Ts`. -/
theorem core_bound {Buyer Seller Item : Type} [Fintype Buyer] [Fintype Seller]
    [DecidableEq Item]
    (E : Exchange Buyer Seller Item ℝ) (hsv : ∀ s Z, E.sval s Z = 0)
    (o : Outcome Buyer Seller Item) (ho : InCore E o)
    (Ts : Finset Seller) (hTs : Ts.Nonempty)
    (c : Buyer → ℝ) (S' : Buyer → Finset Item)
    (hc0 : ∀ b, 0 ≤ c b)
    (hcB : ∀ b, 0 < c b → c b ≤ E.budget b)
    (hcV : ∀ b, 0 < c b → c b ≤ E.bval b (S' b) - buyerPayoff E o b)
    (hdisj : ∀ b₁ b₂ k, 0 < c b₁ → 0 < c b₂ → k ∈ S' b₁ → k ∈ S' b₂ → b₁ = b₂)
    (hsup : ∀ b k, 0 < c b → k ∈ S' b → ∃ s ∈ Ts, k ∈ E.endow s) :
    ∑ b, c b ≤ ∑ s ∈ Ts, o.q s := by
  obtain ⟨hfeas, hcore⟩ := ho
  have hq0 : ∀ s, 0 ≤ o.q s := fun s => (hfeas.2.1 s (Finset.mem_univ _)).2.1
  have hpi : ∀ b, 0 ≤ buyerPayoff E o b := by
    intro b
    have h := (hfeas.1 b (Finset.mem_univ _)).2
    have h' := min_le_right (E.budget b) (E.bval b (o.S b))
    unfold buyerPayoff
    linarith
  by_contra hlt
  push_neg at hlt
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∑ s ∈ Ts, o.q s := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = ∑ b, c b := ⟨_, rfl⟩
  rw [← hQ, ← hX] at hlt
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact Finset.sum_nonneg (fun s _ => hq0 s)
  have hX0 : 0 < X := lt_of_le_of_lt hQ0 hlt
  obtain ⟨r, hQr, hrX⟩ := exists_between hlt
  have hr0 : 0 < r := lt_of_le_of_lt hQ0 hQr
  obtain ⟨Cb, hCb⟩ : ∃ Cb : Finset Buyer, Cb = Finset.univ.filter fun b => 0 < c b :=
    ⟨_, rfl⟩
  have hmem : ∀ b, b ∈ Cb ↔ 0 < c b := by
    intro b
    rw [hCb]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hsumCb : ∑ b ∈ Cb, c b = X := by
    rw [hX, hCb, Finset.sum_filter_of_ne]
    intro b _ hb
    exact lt_of_le_of_ne (hc0 b) (Ne.symm hb)
  have hcard : (0 : ℝ) < (Ts.card : ℝ) := by exact_mod_cast hTs.card_pos
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (r - Q) / Ts.card := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδ]
    exact div_pos (show 0 < r - Q by linarith) hcard
  have hδc : (Ts.card : ℝ) * δ = r - Q := by
    rw [hδ]
    exact mul_div_cancel₀ (r - Q) (ne_of_gt hcard)
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = r / X := ⟨_, rfl⟩
  have htX : t * X = r := by
    rw [ht]
    exact div_mul_cancel₀ r (ne_of_gt hX0)
  have ht0 : 0 ≤ t := by
    rw [ht]
    exact div_nonneg hr0.le hX0.le
  have ht1 : t < 1 := by
    rw [ht]
    exact (div_lt_one hX0).2 hrX
  apply hcore ⟨Cb, Ts⟩ (Or.inr hTs)
  unfold Blocks
  refine ⟨⟨S', E.endow, fun b => t * c b, fun s => o.q s + δ⟩, ?_, ?_, ?_⟩
  · unfold FeasibleFor
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b hb
      have hb' : 0 < c b := (hmem b).1 hb
      have h1 := hcV b hb'
      have h2 := hcB b hb'
      have h3 := hpi b
      have hc' := hc0 b
      have htc : t * c b ≤ c b := by nlinarith [mul_nonneg (sub_nonneg.2 ht1.le) hc']
      refine ⟨mul_nonneg ht0 hc', le_min ?_ ?_⟩
      · show t * c b ≤ E.budget b
        linarith
      · show t * c b ≤ E.bval b (S' b)
        linarith
    · intro s _
      refine ⟨fun x hx => hx, ?_, ?_⟩
      · show 0 ≤ o.q s + δ
        linarith [hq0 s]
      · show E.sval s (E.endow s) ≤ o.q s + δ
        rw [hsv]
        linarith [hq0 s]
    · show ∑ b ∈ Cb, t * c b = ∑ s ∈ Ts, (o.q s + δ)
      rw [← Finset.mul_sum, hsumCb, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← hQ, hδc, htX]
      ring
    · intro k
      show (Cb.filter fun b => k ∈ S' b).card ≤ (Ts.filter fun s => k ∈ E.endow s).card
      by_cases hk : ∃ b ∈ Cb, k ∈ S' b
      · obtain ⟨b, hb, hkb⟩ := hk
        obtain ⟨s, hs, hks⟩ := hsup b k ((hmem b).1 hb) hkb
        have h1 : (Cb.filter fun b => k ∈ S' b).card ≤ 1 := by
          apply Finset.card_le_one.2
          intro a ha a' ha'
          rw [Finset.mem_filter] at ha ha'
          exact hdisj a a' k ((hmem a).1 ha.1) ((hmem a').1 ha'.1) ha.2 ha'.2
        have h2 : 0 < (Ts.filter fun s => k ∈ E.endow s).card :=
          Finset.card_pos.2 ⟨s, Finset.mem_filter.2 ⟨hs, hks⟩⟩
        omega
      · push_neg at hk
        have h0 : (Cb.filter fun b => k ∈ S' b).card = 0 :=
          Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 hk)
        omega
  · intro b hb
    have hb' : 0 < c b := (hmem b).1 hb
    have h1 := hcV b hb'
    have htc : t * c b < c b := by nlinarith [mul_pos (sub_pos.2 ht1) hb']
    show buyerPayoff E o b < E.bval b (S' b) - t * c b
    linarith
  · intro s _
    show o.q s - E.sval s (o.Z s) < (o.q s + δ) - E.sval s (E.endow s)
    rw [hsv, hsv]
    linarith

/-! ### Basic facts about the gadget -/

variable {ϕ : DNF}

lemma hsval (T U V W : ℝ) : ∀ s Z, (gadget ϕ T U V W).sval s Z = 0 := by
  intro s Z
  simp [Exchange.sval, gadget, Bid.value]

/-- The seller owning an item. -/
def owner : GItem ϕ → GSeller ϕ
  | Sum.inl (i, _) => Sum.inl i
  | Sum.inr (Sum.inl (l, _, _)) => Sum.inr (Sum.inl l)
  | Sum.inr (Sum.inr (Sum.inl _)) => Sum.inr (Sum.inr (Sum.inl ()))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => Sum.inr (Sum.inr (Sum.inl ()))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => Sum.inr (Sum.inr (Sum.inr ()))

lemma endow_owner (T U V W : ℝ) (k : GItem ϕ) : k ∈ (gadget ϕ T U V W).endow (owner k) := by
  rcases k with ⟨i, b⟩ | ⟨l, i, i'⟩ | ⟨j, b⟩ | ⟨l, i⟩ | ⟨r, i, b⟩
  · show Sum.inl (i, b) ∈ ({chi i, chiBar i} : Finset (GItem ϕ))
    cases b
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · exact Finset.mem_insert_self _ _
  · show Sum.inr (Sum.inl (l, i, i')) ∈ Tpsi (ϕ := ϕ) l
    exact Finset.mem_image.2 ⟨(i, i'), Finset.mem_univ _, rfl⟩
  · show Sum.inr (Sum.inr (Sum.inl (j, b))) ∈ (Finset.univ.image gam ∪ Finset.univ.image gamBar ∪
        Finset.univ.image fun p : Fin ϕ.numTerms × Fin ϕ.n => phi p.1 p.2 : Finset (GItem ϕ))
    cases b
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩))
  · show Sum.inr (Sum.inr (Sum.inr (Sum.inl (l, i)))) ∈ (Finset.univ.image gam ∪
        Finset.univ.image gamBar ∪
        Finset.univ.image fun p : Fin ϕ.numTerms × Fin ϕ.n => phi p.1 p.2 : Finset (GItem ϕ))
    exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨(l, i), Finset.mem_univ _, rfl⟩)
  · show Sum.inr (Sum.inr (Sum.inr (Sum.inr (r, i, b)))) ∈
      (Finset.univ.image (fun p : Fin 2 × Fin ϕ.n => lam p.1 p.2) ∪
        Finset.univ.image fun p : Fin 2 × Fin ϕ.n => lamBar p.1 p.2 : Finset (GItem ϕ))
    cases b
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨(r, i), Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨(r, i), Finset.mem_univ _, rfl⟩)

lemma owner_of_mem (T U V W : ℝ) (k : GItem ϕ) (s : GSeller ϕ)
    (h : k ∈ (gadget ϕ T U V W).endow s) : s = owner k := by
  rcases s with i | l | ⟨⟩ | ⟨⟩
  · change k ∈ ({chi i, chiBar i} : Finset (GItem ϕ)) at h
    rw [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · rfl
    · rfl
  · change k ∈ Tpsi (ϕ := ϕ) l at h
    obtain ⟨⟨a, b⟩, _, rfl⟩ := Finset.mem_image.1 h
    rfl
  · change k ∈ (Finset.univ.image gam ∪ Finset.univ.image gamBar ∪
        Finset.univ.image fun p : Fin ϕ.numTerms × Fin ϕ.n => phi p.1 p.2 :
          Finset (GItem ϕ)) at h
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_union.1 h with h | h
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 h
        rfl
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 h
        rfl
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 h
      rfl
  · change k ∈ (Finset.univ.image (fun p : Fin 2 × Fin ϕ.n => lam p.1 p.2) ∪
        Finset.univ.image fun p : Fin 2 × Fin ϕ.n => lamBar p.1 p.2 : Finset (GItem ϕ)) at h
    rcases Finset.mem_union.1 h with h | h
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 h
      rfl
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 h
      rfl

/-- In a feasible outcome every item is in the package of at most one buyer. -/
lemma uniq {T U V W : ℝ} {o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)}
    (hf : Feasible (gadget ϕ T U V W) o) {k : GItem ϕ} {b1 b2 : GBuyer ϕ}
    (h1 : k ∈ o.S b1) (h2 : k ∈ o.S b2) : b1 = b2 := by
  have hs := hf.2.2.2 k
  have hZ : ((Coalition.grand (GBuyer ϕ) (GSeller ϕ)).sellers.filter
      fun j => k ∈ o.Z j).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro a ha b hb
    have ha' := (hf.2.1 a (Finset.mem_univ _)).1 (Finset.mem_filter.1 ha).2
    have hb' := (hf.2.1 b (Finset.mem_univ _)).1 (Finset.mem_filter.1 hb).2
    rw [owner_of_mem T U V W k a ha', owner_of_mem T U V W k b hb']
  have hB := Finset.card_le_one.1 (le_trans hs hZ)
  exact hB b1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩) b2
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩)

lemma pay_facts {T U V W : ℝ} {o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)}
    (hf : Feasible (gadget ϕ T U V W) o) (b : GBuyer ϕ) :
    0 ≤ o.p b ∧ o.p b ≤ (gadget ϕ T U V W).budget b ∧
      o.p b ≤ (gadget ϕ T U V W).bval b (o.S b) := by
  have h := hf.1 b (Finset.mem_univ _)
  exact ⟨h.1, le_trans h.2 (min_le_left _ _), le_trans h.2 (min_le_right _ _)⟩

lemma psi_mem_Fpf (l : Fin ϕ.numTerms) (a b : Fin ϕ.n) : psi l a b ∈ Fpf (ϕ := ϕ) l :=
  Finset.mem_union_left _ (Finset.mem_image.2 ⟨(a, b), Finset.mem_univ _, rfl⟩)

lemma phi_mem_Fpf (l : Fin ϕ.numTerms) (a : Fin ϕ.n) : phi l a ∈ Fpf (ϕ := ϕ) l :=
  Finset.mem_union_right _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)

/-! ### Valuations -/

lemma bvalM (T U V W : ℝ) (i : Fin ϕ.n) (S : Finset (GItem ϕ)) :
    (gadget ϕ T U V W).bval (Sum.inl (BKind.M, i)) S =
      max (if Mb i ⊆ S then 2 * V else 0) (max (if Mbar i ⊆ S then 2 * V else 0) 0) :=
  xor2 (Mb i) (Mbar i) (2 * V) (2 * V) S

lemma bvalC (T U V W : ℝ) (κ : BKind) (hκ : κ = BKind.chi1 ∨ κ = BKind.chi2) (i : Fin ϕ.n)
    (S : Finset (GItem ϕ)) :
    (gadget ϕ T U V W).bval (Sum.inl (κ, i)) S =
      max (if ({chi i} : Finset (GItem ϕ)) ⊆ S then V else 0)
        (max (if ({chiBar i} : Finset (GItem ϕ)) ⊆ S then V else 0) 0) := by
  rcases hκ with rfl | rfl
  · exact xor2 ({chi i} : Finset (GItem ϕ)) {chiBar i} V V S
  · exact xor2 ({chi i} : Finset (GItem ϕ)) {chiBar i} V V S

lemma bvalL1 (T U V W : ℝ) (i : Fin ϕ.n) (S : Finset (GItem ϕ)) :
    (gadget ϕ T U V W).bval (Sum.inl (BKind.lam1, i)) S =
      max (if ({lam 0 i} : Finset (GItem ϕ)) ⊆ S then V else 0)
        (max (if ({lamBar 0 i} : Finset (GItem ϕ)) ⊆ S then V - ϕ.numTerms else 0) 0) :=
  xor2 ({lam 0 i} : Finset (GItem ϕ)) {lamBar 0 i} V (V - ϕ.numTerms) S

lemma bvalL2 (T U V W : ℝ) (i : Fin ϕ.n) (S : Finset (GItem ϕ)) :
    (gadget ϕ T U V W).bval (Sum.inl (BKind.lam2, i)) S =
      max (if ({lam 1 i} : Finset (GItem ϕ)) ⊆ S then V - ϕ.numTerms else 0)
        (max (if ({lamBar 1 i} : Finset (GItem ϕ)) ⊆ S then V else 0) 0) :=
  xor2 ({lam 1 i} : Finset (GItem ϕ)) {lamBar 1 i} (V - ϕ.numTerms) V S

lemma bvalK_le (T U V W : ℝ) (hW : 0 ≤ W) (i : Fin ϕ.n) (S : Finset (GItem ϕ)) :
    (gadget ϕ T U V W).bval (Sum.inl (BKind.K, i)) S ≤ W := by
  unfold Exchange.bval
  refine Aux_BCE1.xor_le _ S W hW ?_
  intro b hb _
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
    List.not_mem_nil, or_false] at hb
  obtain ⟨l, hl | hl⟩ := hb <;> rw [hl]

lemma bvalK_ge (T U V W : ℝ) (i : Fin ϕ.n) (l : Fin ϕ.numTerms) (S : Finset (GItem ϕ))
    (h : Kb l i ⊆ S ∨ Kbar l i ⊆ S) :
    W ≤ (gadget ϕ T U V W).bval (Sum.inl (BKind.K, i)) S := by
  unfold Exchange.bval
  rcases h with h | h
  · exact xor_ge ((List.finRange ϕ.numTerms).flatMap fun l => [(Kb l i, W), (Kbar l i, W)])
      S (Kb l i, W) (List.mem_flatMap.2 ⟨l, List.mem_finRange l, List.mem_cons_self⟩) h
  · exact xor_ge ((List.finRange ϕ.numTerms).flatMap fun l => [(Kb l i, W), (Kbar l i, W)])
      S (Kbar l i, W) (List.mem_flatMap.2 ⟨l, List.mem_finRange l,
        List.mem_cons_of_mem _ List.mem_cons_self⟩) h

lemma bvalK_zero (T U V W : ℝ) (i : Fin ϕ.n) (S : Finset (GItem ϕ))
    (h : ∀ l, ¬ Kb l i ⊆ S ∧ ¬ Kbar l i ⊆ S) :
    (gadget ϕ T U V W).bval (Sum.inl (BKind.K, i)) S = 0 := by
  apply le_antisymm
  · unfold Exchange.bval
    refine Aux_BCE1.xor_le _ _ 0 le_rfl ?_
    intro b hb hsub
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
      List.not_mem_nil, or_false] at hb
    obtain ⟨l, hl | hl⟩ := hb
    · rw [hl] at hsub; exact absurd hsub (h l).1
    · rw [hl] at hsub; exact absurd hsub (h l).2
  · exact xor_nonneg _ _

lemma parts_eq {α Item : Type} [DecidableEq Item] (F : α → Finset Item) (S : Finset Item)
    (c : α → Bool) (l0 : List α) :
    ((((l0.filter c).map fun l => (F l, (1 : ℝ))).filter fun p => decide (p.1 ⊆ S)).map
      fun p => p.2).sum = (l0.map fun l => if c l = true ∧ F l ⊆ S then (1 : ℝ) else 0).sum := by
  induction l0 with
  | nil => simp
  | cons a t ih =>
    by_cases hc : c a = true
    · by_cases hs : F a ⊆ S
      · simp only [List.filter_cons, hc, if_true, List.map_cons, hs, decide_true,
          List.sum_cons, and_self]
        linarith
      · simp only [List.filter_cons, hc, if_true, List.map_cons, hs, decide_false,
          List.sum_cons, Bool.false_eq_true, if_false, and_false]
        linarith
    · have hc' : c a = false := by simpa using hc
      simp only [List.filter_cons, hc', List.map_cons, List.sum_cons, Bool.false_eq_true,
        if_false, false_and]
      linarith

lemma grp_formula (x : GItem ϕ) (c : Fin ϕ.numTerms → Bool)
    (P : Fin ϕ.numTerms → Prop) [DecidablePred P] (hc : ∀ l, c l = true ↔ P l)
    (S : Finset (GItem ϕ)) :
    BidGroup.value ⟨{x}, ((List.finRange ϕ.numTerms).filter c).map
        fun l => (Fpf l, (1 : ℝ))⟩ S =
      if x ∈ S then (((Finset.univ.filter fun l => P l ∧ Fpf l ⊆ S).card : ℕ) : ℝ) else 0 := by
  have e : (Finset.univ.filter fun l => c l = true ∧ Fpf l ⊆ S) =
      (Finset.univ.filter fun l => P l ∧ Fpf l ⊆ S) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hc l]
  unfold BidGroup.value
  dsimp only
  by_cases hx : x ∈ S
  · have hx' : ({x} : Finset (GItem ϕ)) ⊆ S := Finset.singleton_subset_iff.2 hx
    rw [if_pos hx', if_pos hx, parts_eq, ← Fin.sum_univ_def, Finset.sum_boole]
    exact congrArg (fun s : Finset (Fin ϕ.numTerms) => ((s.card : ℕ) : ℝ)) e
  · have hx' : ¬ ({x} : Finset (GItem ϕ)) ⊆ S := fun h => hx (Finset.singleton_subset_iff.1 h)
    rw [if_neg hx', if_neg hx]

open Classical in
lemma bvalG (T U V W : ℝ) (j : Fin ϕ.m) (S : Finset (GItem ϕ)) :
    (gadget ϕ T U V W).bval (Sum.inr j) S =
      max (if gam j ∈ S then (((Finset.univ.filter fun l =>
          (Sum.inr j, false) ∈ ϕ.term l ∧ Fpf l ⊆ S).card : ℕ) : ℝ) else 0)
        (max (if gamBar j ∈ S then (((Finset.univ.filter fun l =>
          (Sum.inr j, true) ∈ ϕ.term l ∧ Fpf l ⊆ S).card : ℕ) : ℝ) else 0) 0) := by
  unfold Exchange.bval Bid.value
  show max _ (max _ 0) = _
  refine congrArg₂ max ?_ (congrArg₂ max ?_ rfl)
  · exact grp_formula (gam j) _ (fun l => (Sum.inr j, false) ∈ ϕ.term l)
      (fun l => decide_eq_true_iff) S
  · exact grp_formula (gamBar j) _ (fun l => (Sum.inr j, true) ∈ ϕ.term l)
      (fun l => decide_eq_true_iff) S

lemma max_nat (A B : ℕ) (p q : Prop) [Decidable p] [Decidable q] :
    max (if p then (A : ℝ) else 0) (max (if q then (B : ℝ) else 0) 0) =
      ((max (if p then A else 0) (if q then B else 0) : ℕ) : ℝ) := by
  rw [Nat.cast_max, Nat.cast_ite, Nat.cast_ite, Nat.cast_zero]
  have h : (0 : ℝ) ≤ (if q then (B : ℝ) else 0) := by
    split_ifs
    · exact Nat.cast_nonneg B
    · exact le_refl 0
  rw [max_eq_left h]

open Classical in
lemma bvalG_le (T U V W : ℝ) (j : Fin ϕ.m) (S : Finset (GItem ϕ)) :
    (gadget ϕ T U V W).bval (Sum.inr j) S ≤
      (((Finset.univ.filter fun l : Fin ϕ.numTerms => Fpf l ⊆ S).card : ℕ) : ℝ) := by
  rw [bvalG]
  have h0 : (0 : ℝ) ≤ (((Finset.univ.filter fun l : Fin ϕ.numTerms => Fpf l ⊆ S).card : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have h1 : ∀ (P : Fin ϕ.numTerms → Prop) [DecidablePred P],
      (((Finset.univ.filter fun l => P l ∧ Fpf l ⊆ S).card : ℕ) : ℝ) ≤
        (((Finset.univ.filter fun l : Fin ϕ.numTerms => Fpf l ⊆ S).card : ℕ) : ℝ) := by
    intro P _
    have : (Finset.univ.filter fun l => P l ∧ Fpf l ⊆ S).card ≤
        (Finset.univ.filter fun l : Fin ϕ.numTerms => Fpf l ⊆ S).card :=
      Finset.card_le_card (fun l hl => Finset.mem_filter.2
        ⟨Finset.mem_univ _, (Finset.mem_filter.1 hl).2.2⟩)
    exact_mod_cast this
  refine max_le ?_ (max_le ?_ h0)
  · split_ifs
    · exact h1 (fun l => (Sum.inr j, false) ∈ ϕ.term l)
    · exact h0
  · split_ifs
    · exact h1 (fun l => (Sum.inr j, true) ∈ ϕ.term l)
    · exact h0

lemma bg_sum_le {T U V W : ℝ} {o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)}
    (hf : Feasible (gadget ϕ T U V W) o) (i0 : Fin ϕ.n) :
    ∑ j : Fin ϕ.m, (gadget ϕ T U V W).bval (Sum.inr j) (o.S (Sum.inr j)) ≤
      (((Finset.univ.filter fun l : Fin ϕ.numTerms =>
        ∃ j, Fpf l ⊆ o.S (Sum.inr j)).card : ℕ) : ℝ) := by
  have hdisj : ∀ (l : Fin ϕ.numTerms) (j1 j2 : Fin ϕ.m), Fpf l ⊆ o.S (Sum.inr j1) →
      Fpf l ⊆ o.S (Sum.inr j2) → j1 = j2 := by
    intro l j1 j2 h1 h2
    have hm : psi l i0 i0 ∈ Fpf (ϕ := ϕ) l := psi_mem_Fpf l i0 i0
    exact Sum.inr_injective (uniq hf (h1 hm) (h2 hm))
  have hcol : ∀ l : Fin ϕ.numTerms,
      (∑ j : Fin ϕ.m, if Fpf l ⊆ o.S (Sum.inr j) then (1 : ℝ) else 0) ≤
        if (∃ j, Fpf l ⊆ o.S (Sum.inr j)) then (1 : ℝ) else 0 := by
    intro l
    rw [Finset.sum_boole]
    by_cases hex : ∃ j, Fpf l ⊆ o.S (Sum.inr j)
    · rw [if_pos hex]
      have : (Finset.univ.filter fun j : Fin ϕ.m => Fpf l ⊆ o.S (Sum.inr j)).card ≤ 1 := by
        apply Finset.card_le_one.2
        intro a ha b hb
        exact hdisj l a b (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
      exact_mod_cast this
    · rw [if_neg hex]
      have h0 : (Finset.univ.filter fun j : Fin ϕ.m => Fpf l ⊆ o.S (Sum.inr j)).card = 0 :=
        Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun j _ hj => hex ⟨j, hj⟩)
      exact_mod_cast h0.le
  calc ∑ j : Fin ϕ.m, (gadget ϕ T U V W).bval (Sum.inr j) (o.S (Sum.inr j))
      ≤ ∑ j : Fin ϕ.m, (((Finset.univ.filter fun l : Fin ϕ.numTerms =>
          Fpf l ⊆ o.S (Sum.inr j)).card : ℕ) : ℝ) :=
        Finset.sum_le_sum fun j _ => bvalG_le T U V W j _
    _ = ∑ j : Fin ϕ.m, ∑ l : Fin ϕ.numTerms,
          if Fpf l ⊆ o.S (Sum.inr j) then (1 : ℝ) else 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_boole]
    _ = ∑ l : Fin ϕ.numTerms, ∑ j : Fin ϕ.m,
          if Fpf l ⊆ o.S (Sum.inr j) then (1 : ℝ) else 0 := Finset.sum_comm
    _ ≤ ∑ l : Fin ϕ.numTerms, if (∃ j, Fpf l ⊆ o.S (Sum.inr j)) then (1 : ℝ) else 0 :=
        Finset.sum_le_sum fun l _ => hcol l
    _ = (((Finset.univ.filter fun l : Fin ϕ.numTerms =>
          ∃ j, Fpf l ⊆ o.S (Sum.inr j)).card : ℕ) : ℝ) := by
        rw [Finset.sum_boole]

lemma sum_buyers (f : GBuyer ϕ → ℝ) :
    ∑ b, f b = ∑ k : Fin ϕ.n, (f (Sum.inl (BKind.K, k)) + f (Sum.inl (BKind.M, k)) +
      f (Sum.inl (BKind.chi1, k)) + f (Sum.inl (BKind.chi2, k)) +
      f (Sum.inl (BKind.lam1, k)) + f (Sum.inl (BKind.lam2, k))) +
      ∑ j : Fin ϕ.m, f (Sum.inr j) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Aux_BCE1.sum_BKind]
  simp only [Finset.sum_add_distrib]

/-! ### Item indices -/

/-- The index `i` of the gadget items attached to the variable `xᵢ` (columns of `ψ` by their
column index). -/
def mIdx : GItem ϕ → Option (Fin ϕ.n)
  | Sum.inl (k, _) => some k
  | Sum.inr (Sum.inl (_, _, k)) => some k
  | Sum.inr (Sum.inr (Sum.inl _)) => none
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => none
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (_, k, _)))) => some k

lemma mem_Mb {k : Fin ϕ.n} {x : GItem ϕ} (h : x ∈ Mb k) :
    x = chi k ∨ x = lam 0 k ∨ x = lam 1 k ∨ ∃ l a, x = psi l a k := by
  unfold Mb at h
  rcases Finset.mem_union.1 h with h | h
  · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.1 h
    obtain ⟨a, _, ha⟩ := Finset.mem_image.1 hl
    exact Or.inr (Or.inr (Or.inr ⟨l, a, ha.symm⟩))

lemma mem_Mbar {k : Fin ϕ.n} {x : GItem ϕ} (h : x ∈ Mbar k) :
    x = chiBar k ∨ x = lamBar 0 k ∨ x = lamBar 1 k ∨ ∃ l a, x = psi l a k := by
  unfold Mbar at h
  rcases Finset.mem_union.1 h with h | h
  · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.1 h
    obtain ⟨a, _, ha⟩ := Finset.mem_image.1 hl
    exact Or.inr (Or.inr (Or.inr ⟨l, a, ha.symm⟩))

lemma mIdx_Mb {k : Fin ϕ.n} {x : GItem ϕ} (h : x ∈ Mb k) : mIdx x = some k := by
  rcases mem_Mb h with rfl | rfl | rfl | ⟨l, a, rfl⟩
  · rfl
  · rfl
  · rfl
  · rfl

lemma mIdx_Mbar {k : Fin ϕ.n} {x : GItem ϕ} (h : x ∈ Mbar k) : mIdx x = some k := by
  rcases mem_Mbar h with rfl | rfl | rfl | ⟨l, a, rfl⟩
  · rfl
  · rfl
  · rfl
  · rfl

lemma chi_not_Mbar (i : Fin ϕ.n) : chi i ∉ Mbar (ϕ := ϕ) i := by
  intro h
  rcases mem_Mbar h with h | h | h | ⟨l, a, h⟩ <;> simp [chi, chiBar, lamBar, psi] at h

lemma chiBar_not_Mb (i : Fin ϕ.n) : chiBar i ∉ Mb (ϕ := ϕ) i := by
  intro h
  rcases mem_Mb h with h | h | h | ⟨l, a, h⟩ <;> simp [chi, chiBar, lam, psi] at h

lemma chi_of_K {S : Finset (GItem ϕ)} {k : Fin ϕ.n} (h : ∃ l, Kb l k ⊆ S ∨ Kbar l k ⊆ S) :
    chi k ∈ S ∨ chiBar k ∈ S := by
  obtain ⟨l, hl | hl⟩ := h
  · exact Or.inl (hl (Finset.mem_insert_self _ _))
  · exact Or.inr (hl (Finset.mem_insert_self _ _))

/-! ### The χ-buyers -/

noncomputable def chiOf (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (k : Fin ϕ.n) :
    GItem ϕ :=
  if chi k ∈ o.S (Sum.inl (BKind.K, k)) then chi k else chiBar k

noncomputable def chiOth (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (k : Fin ϕ.n) :
    GItem ϕ :=
  if chi k ∈ o.S (Sum.inl (BKind.K, k)) then chiBar k else chi k

noncomputable def idleK (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (k : Fin ϕ.n) : BKind :=
  if chiOth o k ∈ o.S (Sum.inl (BKind.chi1, k)) then BKind.chi2 else BKind.chi1

lemma chi_cases (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (k : Fin ϕ.n) :
    (chiOf o k = chi k ∧ chiOth o k = chiBar k) ∨
      (chiOf o k = chiBar k ∧ chiOth o k = chi k) := by
  unfold chiOf chiOth
  by_cases h : chi k ∈ o.S (Sum.inl (BKind.K, k))
  · exact Or.inl ⟨if_pos h, if_pos h⟩
  · exact Or.inr ⟨if_neg h, if_neg h⟩

lemma chiOf_mem (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (k : Fin ϕ.n)
    (h : chi k ∈ o.S (Sum.inl (BKind.K, k)) ∨ chiBar k ∈ o.S (Sum.inl (BKind.K, k))) :
    chiOf o k ∈ o.S (Sum.inl (BKind.K, k)) := by
  unfold chiOf
  by_cases h' : chi k ∈ o.S (Sum.inl (BKind.K, k))
  · rw [if_pos h']
    exact h'
  · rw [if_neg h']
    exact h.resolve_left h'

lemma chiOf_idx (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (k : Fin ϕ.n) :
    mIdx (chiOf o k) = some k := by
  rcases chi_cases o k with ⟨e, _⟩ | ⟨e, _⟩
  · rw [e]; rfl
  · rw [e]; rfl

lemma idleK_cases (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (k : Fin ϕ.n) :
    idleK o k = BKind.chi1 ∨ idleK o k = BKind.chi2 := by
  unfold idleK
  by_cases h : chiOth o k ∈ o.S (Sum.inl (BKind.chi1, k))
  · exact Or.inr (if_pos h)
  · exact Or.inl (if_neg h)

lemma neither_of (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (k : Fin ϕ.n)
    (S : Finset (GItem ϕ)) (h1 : chiOf o k ∉ S) (h2 : chiOth o k ∉ S) :
    chi k ∉ S ∧ chiBar k ∉ S := by
  rcases chi_cases o k with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1] at h1
    rw [e2] at h2
    exact ⟨h1, h2⟩
  · rw [e1] at h1
    rw [e2] at h2
    exact ⟨h2, h1⟩

lemma chiv_zero (T U V W : ℝ) (κ : BKind) (hκ : κ = BKind.chi1 ∨ κ = BKind.chi2)
    (k : Fin ϕ.n) (S : Finset (GItem ϕ)) (h1 : chi k ∉ S) (h2 : chiBar k ∉ S) :
    (gadget ϕ T U V W).bval (Sum.inl (κ, k)) S = 0 := by
  rw [bvalC T U V W κ hκ k S]
  have h1' : ¬ ({chi k} : Finset (GItem ϕ)) ⊆ S := fun h => h1 (Finset.singleton_subset_iff.1 h)
  have h2' : ¬ ({chiBar k} : Finset (GItem ϕ)) ⊆ S :=
    fun h => h2 (Finset.singleton_subset_iff.1 h)
  rw [if_neg h1', if_neg h2']
  simp only [max_self]

lemma notK_of_chi {T U V W : ℝ} {o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)}
    (hf : Feasible (gadget ϕ T U V W) o) (κ : BKind) (hκ : κ = BKind.chi1 ∨ κ = BKind.chi2)
    (k : Fin ϕ.n) (hm : chiOf o k ∈ o.S (Sum.inl (BKind.K, k))) :
    chiOf o k ∉ o.S (Sum.inl (κ, k)) := by
  intro h
  have e := uniq hf h hm
  have e2 : κ = BKind.K := (Prod.mk.inj (Sum.inl_injective e)).1
  rcases hκ with h1 | h1
  · rw [h1] at e2
    exact absurd e2 (by decide)
  · rw [h1] at e2
    exact absurd e2 (by decide)

lemma idle_not_chiOth {T U V W : ℝ} {o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)}
    (hf : Feasible (gadget ϕ T U V W) o) (k : Fin ϕ.n) :
    chiOth o k ∉ o.S (Sum.inl (idleK o k, k)) := by
  unfold idleK
  by_cases h : chiOth o k ∈ o.S (Sum.inl (BKind.chi1, k))
  · rw [if_pos h]
    intro h2
    have e := uniq hf h h2
    have e2 : BKind.chi1 = BKind.chi2 := (Prod.mk.inj (Sum.inl_injective e)).1
    exact absurd e2 (by decide)
  · rw [if_neg h]
    exact h

lemma idle_val {T U V W : ℝ} {o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)}
    (hf : Feasible (gadget ϕ T U V W) o) (k : Fin ϕ.n)
    (hm : chiOf o k ∈ o.S (Sum.inl (BKind.K, k))) :
    (gadget ϕ T U V W).bval (Sum.inl (idleK o k, k)) (o.S (Sum.inl (idleK o k, k))) = 0 := by
  have h1 := notK_of_chi hf (idleK o k) (idleK_cases o k) k hm
  have h2 := idle_not_chiOth hf k
  have h3 := neither_of o k _ h1 h2
  exact chiv_zero T U V W (idleK o k) (idleK_cases o k) k _ h3.1 h3.2

lemma idle_single (T U V W : ℝ) (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (k : Fin ϕ.n) :
    V ≤ (gadget ϕ T U V W).bval (Sum.inl (idleK o k, k)) {chiOf o k} := by
  rw [bvalC T U V W (idleK o k) (idleK_cases o k) k]
  rcases chi_cases o k with ⟨e1, _⟩ | ⟨e1, _⟩
  · rw [e1]
    have h : ({chi k} : Finset (GItem ϕ)) ⊆ {chi k} := Finset.Subset.refl _
    rw [if_pos h]
    exact le_max_left _ _
  · rw [e1]
    have h : ({chiBar k} : Finset (GItem ϕ)) ⊆ {chiBar k} := Finset.Subset.refl _
    rw [if_pos h]
    exact le_trans (le_max_left _ _) (le_max_right _ _)

lemma chi_pay {T U V W : ℝ} {o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)}
    (hf : Feasible (gadget ϕ T U V W) o) (k : Fin ϕ.n)
    (hm : chiOf o k ∈ o.S (Sum.inl (BKind.K, k))) :
    o.p (Sum.inl (BKind.chi1, k)) + o.p (Sum.inl (BKind.chi2, k)) ≤ V := by
  have hz : ∀ κ : BKind, (κ = BKind.chi1 ∨ κ = BKind.chi2) →
      chiOth o k ∉ o.S (Sum.inl (κ, k)) → o.p (Sum.inl (κ, k)) = 0 := by
    intro κ hκ hn
    have hnf := notK_of_chi hf κ hκ k hm
    have h3 := neither_of o k _ hnf hn
    have hv := chiv_zero T U V W κ hκ k _ h3.1 h3.2
    have hp := pay_facts hf (Sum.inl (κ, k))
    have hp1 := hp.1
    have hp2 := hp.2.2
    linarith
  have hle : ∀ κ : BKind, (κ = BKind.chi1 ∨ κ = BKind.chi2) → o.p (Sum.inl (κ, k)) ≤ V := by
    intro κ hκ
    have hp := (pay_facts hf (Sum.inl (κ, k))).2.1
    have hb : (gadget ϕ T U V W).budget (Sum.inl (κ, k)) = V := by
      rcases hκ with rfl | rfl
      · rfl
      · rfl
    linarith
  by_cases h1 : chiOth o k ∈ o.S (Sum.inl (BKind.chi1, k))
  · have h2 : chiOth o k ∉ o.S (Sum.inl (BKind.chi2, k)) := by
      intro h2
      have e := uniq hf h1 h2
      have e2 : BKind.chi1 = BKind.chi2 := (Prod.mk.inj (Sum.inl_injective e)).1
      exact absurd e2 (by decide)
    have ha := hz BKind.chi2 (Or.inr rfl) h2
    have hb := hle BKind.chi1 (Or.inl rfl)
    linarith
  · have ha := hz BKind.chi1 (Or.inl rfl) h1
    have hb := hle BKind.chi2 (Or.inr rfl)
    linarith

lemma disj_idx (B N : Finset (GItem ϕ)) (k i : Fin ϕ.n) (hki : k ≠ i)
    (hB : ∀ x ∈ B, mIdx x = some k) (hN : ∀ x ∈ N, mIdx x = some i) : Disjoint B N :=
  Finset.disjoint_left.2 fun x hx hy =>
    hki (Option.some_injective _ ((hB x hx).symm.trans (hN x hy)))

lemma idx_single (x : GItem ϕ) (k : Fin ϕ.n) (h : mIdx x = some k) :
    ∀ y ∈ ({x} : Finset (GItem ϕ)), mIdx y = some k := by
  intro y hy
  obtain rfl := Finset.mem_singleton.1 hy
  exact h

/-! ### Lemma 3: the reallocation giving `Bᴹᵢ` a bundle -/

noncomputable def NN (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (i : Fin ϕ.n) :
    Finset (GItem ϕ) :=
  if chi i ∈ o.S (Sum.inl (BKind.K, i)) then Mbar i else Mb i

lemma NN_idx (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (i : Fin ϕ.n) :
    ∀ x ∈ NN o i, mIdx x = some i := by
  intro x h
  unfold NN at h
  by_cases hc : chi i ∈ o.S (Sum.inl (BKind.K, i))
  · rw [if_pos hc] at h
    exact mIdx_Mbar h
  · rw [if_neg hc] at h
    exact mIdx_Mb h

lemma chiOf_not_NN (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (i : Fin ϕ.n) :
    chiOf o i ∉ NN o i := by
  unfold NN chiOf
  by_cases h : chi i ∈ o.S (Sum.inl (BKind.K, i))
  · simp only [if_pos h]
    exact chi_not_Mbar i
  · simp only [if_neg h]
    exact chiBar_not_Mb i

lemma chiOf_not_NN_all (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (i k : Fin ϕ.n) :
    chiOf o k ∉ NN o i := by
  by_cases hk : k = i
  · rw [hk]
    exact chiOf_not_NN o i
  · intro h
    exact hk (Option.some_injective _ ((chiOf_idx o k).symm.trans (NN_idx o i _ h)))

lemma NN_val (T U V W : ℝ) (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (i : Fin ϕ.n) :
    2 * V ≤ (gadget ϕ T U V W).bval (Sum.inl (BKind.M, i)) (NN o i) := by
  rw [bvalM]
  unfold NN
  by_cases h : chi i ∈ o.S (Sum.inl (BKind.K, i))
  · simp only [if_pos h]
    have hs : Mbar i ⊆ Mbar (ϕ := ϕ) i := Finset.Subset.refl _
    rw [if_pos hs]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  · simp only [if_neg h]
    have hs : Mb i ⊆ Mb (ϕ := ϕ) i := Finset.Subset.refl _
    rw [if_pos hs]
    exact le_max_left _ _

noncomputable def c3 (V : ℝ) (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (i : Fin ϕ.n) :
    GBuyer ϕ → ℝ
  | Sum.inl (BKind.K, k) =>
      if Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) then o.p (Sum.inl (BKind.K, k)) else 0
  | Sum.inl (BKind.M, k) => if k = i then 2 * V else o.p (Sum.inl (BKind.M, k))
  | Sum.inl (BKind.chi1, k) =>
      if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧ idleK o k = BKind.chi1 then V
      else if k = i then 0 else o.p (Sum.inl (BKind.chi1, k))
  | Sum.inl (BKind.chi2, k) =>
      if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧ idleK o k = BKind.chi2 then V
      else if k = i then 0 else o.p (Sum.inl (BKind.chi2, k))
  | Sum.inl (BKind.lam1, k) => if k = i then 0 else o.p (Sum.inl (BKind.lam1, k))
  | Sum.inl (BKind.lam2, k) => if k = i then 0 else o.p (Sum.inl (BKind.lam2, k))
  | Sum.inr _ => 0

noncomputable def S3 (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (i : Fin ϕ.n) :
    GBuyer ϕ → Finset (GItem ϕ)
  | Sum.inl (BKind.K, k) => o.S (Sum.inl (BKind.K, k)) \ NN o i
  | Sum.inl (BKind.M, k) => if k = i then NN o i else o.S (Sum.inl (BKind.M, k)) \ NN o i
  | Sum.inl (BKind.chi1, k) =>
      if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧ idleK o k = BKind.chi1 then
        {chiOf o k}
      else o.S (Sum.inl (BKind.chi1, k)) \ NN o i
  | Sum.inl (BKind.chi2, k) =>
      if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧ idleK o k = BKind.chi2 then
        {chiOf o k}
      else o.S (Sum.inl (BKind.chi2, k)) \ NN o i
  | Sum.inl (BKind.lam1, k) => o.S (Sum.inl (BKind.lam1, k)) \ NN o i
  | Sum.inl (BKind.lam2, k) => o.S (Sum.inl (BKind.lam2, k)) \ NN o i
  | Sum.inr j => o.S (Sum.inr j) \ NN o i

lemma classify3 (V : ℝ) (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (i : Fin ϕ.n)
    (b : GBuyer ϕ) (hb : 0 < c3 V o i b) :
    (b = Sum.inl (BKind.M, i) ∧ S3 o i b = NN o i) ∨
    (∃ k, ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧ b = Sum.inl (idleK o k, k) ∧
      S3 o i b = {chiOf o k}) ∨
    (S3 o i b = o.S b \ NN o i ∧
      ∀ k, b = Sum.inl (BKind.K, k) → Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i)) := by
  rcases b with ⟨κ, k⟩ | j
  · cases κ
    · change 0 < (if Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) then
        o.p (Sum.inl (BKind.K, k)) else 0) at hb
      by_cases hd : Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i)
      · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
        intro k' e
        have hk : k = k' := (Prod.mk.inj (Sum.inl_injective e)).2
        rw [← hk]
        exact hd
      · rw [if_neg hd] at hb
        exact absurd hb (lt_irrefl 0)
    · by_cases hk : k = i
      · left
        rw [hk]
        exact ⟨rfl, if_pos (rfl : i = i)⟩
      · refine Or.inr (Or.inr ⟨if_neg hk, ?_⟩)
        intro k' e
        have e2 : BKind.M = BKind.K := (Prod.mk.inj (Sum.inl_injective e)).1
        exact absurd e2 (by decide)
    · change 0 < (if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
        idleK o k = BKind.chi1 then V else if k = i then 0 else
          o.p (Sum.inl (BKind.chi1, k))) at hb
      by_cases hc : ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧ idleK o k = BKind.chi1
      · refine Or.inr (Or.inl ⟨k, hc.1, ?_, if_pos hc⟩)
        rw [hc.2]
      · refine Or.inr (Or.inr ⟨if_neg hc, ?_⟩)
        intro k' e
        have e2 : BKind.chi1 = BKind.K := (Prod.mk.inj (Sum.inl_injective e)).1
        exact absurd e2 (by decide)
    · change 0 < (if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
        idleK o k = BKind.chi2 then V else if k = i then 0 else
          o.p (Sum.inl (BKind.chi2, k))) at hb
      by_cases hc : ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧ idleK o k = BKind.chi2
      · refine Or.inr (Or.inl ⟨k, hc.1, ?_, if_pos hc⟩)
        rw [hc.2]
      · refine Or.inr (Or.inr ⟨if_neg hc, ?_⟩)
        intro k' e
        have e2 : BKind.chi2 = BKind.K := (Prod.mk.inj (Sum.inl_injective e)).1
        exact absurd e2 (by decide)
    · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
      intro k' e
      have e2 : BKind.lam1 = BKind.K := (Prod.mk.inj (Sum.inl_injective e)).1
      exact absurd e2 (by decide)
    · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
      intro k' e
      have e2 : BKind.lam2 = BKind.K := (Prod.mk.inj (Sum.inl_injective e)).1
      exact absurd e2 (by decide)
  · exact absurd hb (lt_irrefl 0)

lemma lemma3_main (ϕ : DNF) (T U V W : ℝ) (hA : Admissible ϕ T U V W)
    (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (ho : IsNWEquilibrium ϕ T U V W o)
    (i : Fin ϕ.n) :
    Mb i ⊆ o.S (Sum.inl (BKind.M, i)) ∨ Mbar i ⊆ o.S (Sum.inl (BKind.M, i)) := by
  have hK : ∀ k, ∃ l : Fin ϕ.numTerms,
      Kb l k ⊆ o.S (Sum.inl (BKind.K, k)) ∨ Kbar l k ⊆ o.S (Sum.inl (BKind.K, k)) :=
    fun k => Aux_BCE1.main ϕ T U V W hA o ho k
  obtain ⟨l0, _⟩ := hK i
  obtain ⟨hT0, hT1, hU, hV, hW⟩ := hA
  have hcoreIn : InCore (gadget ϕ T U V W) o := ho.1
  have hfeas : Feasible (gadget ϕ T U V W) o := hcoreIn.1
  have hn1 : (1 : ℝ) ≤ ϕ.n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Fin.pos i).ne'
  have hL1 : (1 : ℝ) ≤ ϕ.numTerms := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Fin.pos l0).ne'
  have hnL : (ϕ.numTerms : ℝ) ≤ ϕ.n * ϕ.numTerms := by
    nlinarith [mul_nonneg (sub_nonneg.2 hn1) (sub_nonneg.2 hL1)]
  have hLU : (ϕ.numTerms : ℝ) < U := by linarith
  have h1U : (1 : ℝ) < U := by linarith
  have hV0 : 0 < V := by linarith
  have hmemK : ∀ k, chiOf o k ∈ o.S (Sum.inl (BKind.K, k)) :=
    fun k => chiOf_mem o k (chi_of_K (hK k))
  by_contra hno
  have hno1 : ¬ Mb i ⊆ o.S (Sum.inl (BKind.M, i)) := fun h => hno (Or.inl h)
  have hno2 : ¬ Mbar i ⊆ o.S (Sum.inl (BKind.M, i)) := fun h => hno (Or.inr h)
  have hM0 : (gadget ϕ T U V W).bval (Sum.inl (BKind.M, i)) (o.S (Sum.inl (BKind.M, i))) = 0 := by
    rw [bvalM, if_neg hno1, if_neg hno2]
    simp only [max_self]
  have hpM0 : o.p (Sum.inl (BKind.M, i)) = 0 := by
    have h := pay_facts hfeas (Sum.inl (BKind.M, i))
    have h1 := h.1
    have h2 := h.2.2
    linarith
  -- the hypotheses of `core_bound`
  have hc0 : ∀ b, 0 ≤ c3 V o i b := by
    intro b
    rcases b with ⟨κ, k⟩ | j
    · cases κ
      · show 0 ≤ (if Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) then
          o.p (Sum.inl (BKind.K, k)) else 0)
        split_ifs
        · exact (pay_facts hfeas _).1
        · exact le_refl 0
      · show 0 ≤ (if k = i then 2 * V else o.p (Sum.inl (BKind.M, k)))
        split_ifs
        · linarith
        · exact (pay_facts hfeas _).1
      · show 0 ≤ (if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
          idleK o k = BKind.chi1 then V else if k = i then 0 else
            o.p (Sum.inl (BKind.chi1, k)))
        split_ifs
        · exact hV0.le
        · exact le_refl 0
        · exact (pay_facts hfeas _).1
      · show 0 ≤ (if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
          idleK o k = BKind.chi2 then V else if k = i then 0 else
            o.p (Sum.inl (BKind.chi2, k)))
        split_ifs
        · exact hV0.le
        · exact le_refl 0
        · exact (pay_facts hfeas _).1
      · show 0 ≤ (if k = i then 0 else o.p (Sum.inl (BKind.lam1, k)))
        split_ifs
        · exact le_refl 0
        · exact (pay_facts hfeas _).1
      · show 0 ≤ (if k = i then 0 else o.p (Sum.inl (BKind.lam2, k)))
        split_ifs
        · exact le_refl 0
        · exact (pay_facts hfeas _).1
    · exact le_refl (0 : ℝ)
  have hcB : ∀ b, 0 < c3 V o i b → c3 V o i b ≤ (gadget ϕ T U V W).budget b := by
    intro b
    rcases b with ⟨κ, k⟩ | j
    · cases κ
      · show 0 < (if Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) then
          o.p (Sum.inl (BKind.K, k)) else 0) → (if Disjoint (o.S (Sum.inl (BKind.K, k)))
            (NN o i) then o.p (Sum.inl (BKind.K, k)) else 0) ≤
              (gadget ϕ T U V W).budget (Sum.inl (BKind.K, k))
        intro _
        split_ifs
        · exact (pay_facts hfeas _).2.1
        · exact le_trans (pay_facts hfeas _).1 (pay_facts hfeas _).2.1
      · show 0 < (if k = i then 2 * V else o.p (Sum.inl (BKind.M, k))) →
          (if k = i then 2 * V else o.p (Sum.inl (BKind.M, k))) ≤
            (gadget ϕ T U V W).budget (Sum.inl (BKind.M, k))
        intro _
        split_ifs
        · exact le_refl (2 * V)
        · exact (pay_facts hfeas _).2.1
      · show 0 < (if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
          idleK o k = BKind.chi1 then V else if k = i then 0 else
            o.p (Sum.inl (BKind.chi1, k))) →
          (if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
          idleK o k = BKind.chi1 then V else if k = i then 0 else
            o.p (Sum.inl (BKind.chi1, k))) ≤
              (gadget ϕ T U V W).budget (Sum.inl (BKind.chi1, k))
        intro h
        split_ifs at h ⊢
        · exact le_refl V
        · exact absurd h (lt_irrefl 0)
        · exact (pay_facts hfeas _).2.1
      · show 0 < (if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
          idleK o k = BKind.chi2 then V else if k = i then 0 else
            o.p (Sum.inl (BKind.chi2, k))) →
          (if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
          idleK o k = BKind.chi2 then V else if k = i then 0 else
            o.p (Sum.inl (BKind.chi2, k))) ≤
              (gadget ϕ T U V W).budget (Sum.inl (BKind.chi2, k))
        intro h
        split_ifs at h ⊢
        · exact le_refl V
        · exact absurd h (lt_irrefl 0)
        · exact (pay_facts hfeas _).2.1
      · show 0 < (if k = i then 0 else o.p (Sum.inl (BKind.lam1, k))) →
          (if k = i then 0 else o.p (Sum.inl (BKind.lam1, k))) ≤
            (gadget ϕ T U V W).budget (Sum.inl (BKind.lam1, k))
        intro h
        split_ifs at h ⊢
        · exact absurd h (lt_irrefl 0)
        · exact (pay_facts hfeas _).2.1
      · show 0 < (if k = i then 0 else o.p (Sum.inl (BKind.lam2, k))) →
          (if k = i then 0 else o.p (Sum.inl (BKind.lam2, k))) ≤
            (gadget ϕ T U V W).budget (Sum.inl (BKind.lam2, k))
        intro h
        split_ifs at h ⊢
        · exact absurd h (lt_irrefl 0)
        · exact (pay_facts hfeas _).2.1
    · intro h
      exact absurd h (lt_irrefl 0)
  have hcV : ∀ b, 0 < c3 V o i b →
      c3 V o i b ≤ (gadget ϕ T U V W).bval b (S3 o i b) -
        buyerPayoff (gadget ϕ T U V W) o b := by
    intro b
    rcases b with ⟨κ, k⟩ | j
    · cases κ
      · show 0 < (if Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) then
          o.p (Sum.inl (BKind.K, k)) else 0) → (if Disjoint (o.S (Sum.inl (BKind.K, k)))
            (NN o i) then o.p (Sum.inl (BKind.K, k)) else 0) ≤
              (gadget ϕ T U V W).bval (Sum.inl (BKind.K, k))
                (o.S (Sum.inl (BKind.K, k)) \ NN o i) -
              ((gadget ϕ T U V W).bval (Sum.inl (BKind.K, k)) (o.S (Sum.inl (BKind.K, k))) -
                o.p (Sum.inl (BKind.K, k)))
        intro h
        by_cases hd : Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i)
        · rw [if_pos hd, Finset.sdiff_eq_self_of_disjoint hd]
          linarith
        · rw [if_neg hd] at h
          exact absurd h (lt_irrefl 0)
      · show 0 < (if k = i then 2 * V else o.p (Sum.inl (BKind.M, k))) →
          (if k = i then 2 * V else o.p (Sum.inl (BKind.M, k))) ≤
            (gadget ϕ T U V W).bval (Sum.inl (BKind.M, k))
              (if k = i then NN o i else o.S (Sum.inl (BKind.M, k)) \ NN o i) -
            ((gadget ϕ T U V W).bval (Sum.inl (BKind.M, k)) (o.S (Sum.inl (BKind.M, k))) -
              o.p (Sum.inl (BKind.M, k)))
        intro _
        by_cases hk : k = i
        · rw [hk, if_pos (rfl : i = i), if_pos (rfl : i = i), hM0, hpM0]
          have := NN_val T U V W o i
          linarith
        · rw [if_neg hk, if_neg hk]
          have e : (gadget ϕ T U V W).bval (Sum.inl (BKind.M, k))
              (o.S (Sum.inl (BKind.M, k)) \ NN o i) =
              (gadget ϕ T U V W).bval (Sum.inl (BKind.M, k)) (o.S (Sum.inl (BKind.M, k))) := by
            refine xor_sdiff [(Mb k, 2 * V), (Mbar k, 2 * V)] _ _ ?_
            intro b hb
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
            rcases hb with rfl | rfl
            · exact disj_idx _ _ k i hk (fun x hx => mIdx_Mb hx) (NN_idx o i)
            · exact disj_idx _ _ k i hk (fun x hx => mIdx_Mbar hx) (NN_idx o i)
          rw [e]
          linarith
      · show 0 < (if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
          idleK o k = BKind.chi1 then V else if k = i then 0 else
            o.p (Sum.inl (BKind.chi1, k))) →
          (if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
          idleK o k = BKind.chi1 then V else if k = i then 0 else
            o.p (Sum.inl (BKind.chi1, k))) ≤
            (gadget ϕ T U V W).bval (Sum.inl (BKind.chi1, k))
              (if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
                idleK o k = BKind.chi1 then {chiOf o k}
              else o.S (Sum.inl (BKind.chi1, k)) \ NN o i) -
            ((gadget ϕ T U V W).bval (Sum.inl (BKind.chi1, k)) (o.S (Sum.inl (BKind.chi1, k))) -
              o.p (Sum.inl (BKind.chi1, k)))
        intro h
        by_cases hc : ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧ idleK o k = BKind.chi1
        · rw [if_pos hc, if_pos hc]
          have h1 := idle_single T U V W o k
          have h2 := idle_val hfeas k (hmemK k)
          rw [hc.2] at h1 h2
          have h3 := (pay_facts hfeas (Sum.inl (BKind.chi1, k))).1
          linarith
        · rw [if_neg hc] at h ⊢
          rw [if_neg hc]
          by_cases hk : k = i
          · rw [if_pos hk] at h
            exact absurd h (lt_irrefl 0)
          · rw [if_neg hk]
            have e : (gadget ϕ T U V W).bval (Sum.inl (BKind.chi1, k))
                (o.S (Sum.inl (BKind.chi1, k)) \ NN o i) =
                (gadget ϕ T U V W).bval (Sum.inl (BKind.chi1, k))
                  (o.S (Sum.inl (BKind.chi1, k))) := by
              refine xor_sdiff [(({chi k} : Finset (GItem ϕ)), V), ({chiBar k}, V)] _ _ ?_
              intro b hb
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
              rcases hb with rfl | rfl
              · exact disj_idx _ _ k i hk (idx_single (chi k) k rfl) (NN_idx o i)
              · exact disj_idx _ _ k i hk (idx_single (chiBar k) k rfl) (NN_idx o i)
            rw [e]
            linarith
      · show 0 < (if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
          idleK o k = BKind.chi2 then V else if k = i then 0 else
            o.p (Sum.inl (BKind.chi2, k))) →
          (if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
          idleK o k = BKind.chi2 then V else if k = i then 0 else
            o.p (Sum.inl (BKind.chi2, k))) ≤
            (gadget ϕ T U V W).bval (Sum.inl (BKind.chi2, k))
              (if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
                idleK o k = BKind.chi2 then {chiOf o k}
              else o.S (Sum.inl (BKind.chi2, k)) \ NN o i) -
            ((gadget ϕ T U V W).bval (Sum.inl (BKind.chi2, k)) (o.S (Sum.inl (BKind.chi2, k))) -
              o.p (Sum.inl (BKind.chi2, k)))
        intro h
        by_cases hc : ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧ idleK o k = BKind.chi2
        · rw [if_pos hc, if_pos hc]
          have h1 := idle_single T U V W o k
          have h2 := idle_val hfeas k (hmemK k)
          rw [hc.2] at h1 h2
          have h3 := (pay_facts hfeas (Sum.inl (BKind.chi2, k))).1
          linarith
        · rw [if_neg hc] at h ⊢
          rw [if_neg hc]
          by_cases hk : k = i
          · rw [if_pos hk] at h
            exact absurd h (lt_irrefl 0)
          · rw [if_neg hk]
            have e : (gadget ϕ T U V W).bval (Sum.inl (BKind.chi2, k))
                (o.S (Sum.inl (BKind.chi2, k)) \ NN o i) =
                (gadget ϕ T U V W).bval (Sum.inl (BKind.chi2, k))
                  (o.S (Sum.inl (BKind.chi2, k))) := by
              refine xor_sdiff [(({chi k} : Finset (GItem ϕ)), V), ({chiBar k}, V)] _ _ ?_
              intro b hb
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
              rcases hb with rfl | rfl
              · exact disj_idx _ _ k i hk (idx_single (chi k) k rfl) (NN_idx o i)
              · exact disj_idx _ _ k i hk (idx_single (chiBar k) k rfl) (NN_idx o i)
            rw [e]
            linarith
      · show 0 < (if k = i then 0 else o.p (Sum.inl (BKind.lam1, k))) →
          (if k = i then 0 else o.p (Sum.inl (BKind.lam1, k))) ≤
            (gadget ϕ T U V W).bval (Sum.inl (BKind.lam1, k))
              (o.S (Sum.inl (BKind.lam1, k)) \ NN o i) -
            ((gadget ϕ T U V W).bval (Sum.inl (BKind.lam1, k)) (o.S (Sum.inl (BKind.lam1, k))) -
              o.p (Sum.inl (BKind.lam1, k)))
        intro h
        by_cases hk : k = i
        · rw [if_pos hk] at h
          exact absurd h (lt_irrefl 0)
        · rw [if_neg hk]
          have e : (gadget ϕ T U V W).bval (Sum.inl (BKind.lam1, k))
              (o.S (Sum.inl (BKind.lam1, k)) \ NN o i) =
              (gadget ϕ T U V W).bval (Sum.inl (BKind.lam1, k))
                (o.S (Sum.inl (BKind.lam1, k))) := by
            refine xor_sdiff [(({lam 0 k} : Finset (GItem ϕ)), V), ({lamBar 0 k}, V - ϕ.numTerms)] _ _ ?_
            intro b hb
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
            rcases hb with rfl | rfl
            · exact disj_idx _ _ k i hk (idx_single (lam 0 k) k rfl) (NN_idx o i)
            · exact disj_idx _ _ k i hk (idx_single (lamBar 0 k) k rfl) (NN_idx o i)
          rw [e]
          linarith
      · show 0 < (if k = i then 0 else o.p (Sum.inl (BKind.lam2, k))) →
          (if k = i then 0 else o.p (Sum.inl (BKind.lam2, k))) ≤
            (gadget ϕ T U V W).bval (Sum.inl (BKind.lam2, k))
              (o.S (Sum.inl (BKind.lam2, k)) \ NN o i) -
            ((gadget ϕ T U V W).bval (Sum.inl (BKind.lam2, k)) (o.S (Sum.inl (BKind.lam2, k))) -
              o.p (Sum.inl (BKind.lam2, k)))
        intro h
        by_cases hk : k = i
        · rw [if_pos hk] at h
          exact absurd h (lt_irrefl 0)
        · rw [if_neg hk]
          have e : (gadget ϕ T U V W).bval (Sum.inl (BKind.lam2, k))
              (o.S (Sum.inl (BKind.lam2, k)) \ NN o i) =
              (gadget ϕ T U V W).bval (Sum.inl (BKind.lam2, k))
                (o.S (Sum.inl (BKind.lam2, k))) := by
            refine xor_sdiff [(({lam 1 k} : Finset (GItem ϕ)), V - ϕ.numTerms), ({lamBar 1 k}, V)] _ _ ?_
            intro b hb
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
            rcases hb with rfl | rfl
            · exact disj_idx _ _ k i hk (idx_single (lam 1 k) k rfl) (NN_idx o i)
            · exact disj_idx _ _ k i hk (idx_single (lamBar 1 k) k rfl) (NN_idx o i)
          rw [e]
          linarith
    · intro h
      exact absurd h (lt_irrefl 0)
  have hdisj : ∀ b₁ b₂ x, 0 < c3 V o i b₁ → 0 < c3 V o i b₂ → x ∈ S3 o i b₁ →
      x ∈ S3 o i b₂ → b₁ = b₂ := by
    intro b₁ b₂ x h₁ h₂ hx₁ hx₂
    rcases classify3 V o i b₁ h₁ with ⟨e₁, s₁⟩ | ⟨k₁, d₁, e₁, s₁⟩ | ⟨s₁, n₁⟩ <;>
    rcases classify3 V o i b₂ h₂ with ⟨e₂, s₂⟩ | ⟨k₂, d₂, e₂, s₂⟩ | ⟨s₂, n₂⟩ <;>
    rw [s₁] at hx₁ <;> rw [s₂] at hx₂
    · exact e₁.trans e₂.symm
    · obtain rfl := Finset.mem_singleton.1 hx₂
      exact absurd hx₁ (chiOf_not_NN_all o i k₂)
    · exact absurd hx₁ (Finset.mem_sdiff.1 hx₂).2
    · obtain rfl := Finset.mem_singleton.1 hx₁
      exact absurd hx₂ (chiOf_not_NN_all o i k₁)
    · obtain rfl := Finset.mem_singleton.1 hx₁
      have e := Finset.mem_singleton.1 hx₂
      have hk : k₁ = k₂ := Option.some_injective _
        ((chiOf_idx o k₁).symm.trans ((congrArg mIdx e).trans (chiOf_idx o k₂)))
      subst hk
      exact e₁.trans e₂.symm
    · obtain rfl := Finset.mem_singleton.1 hx₁
      have hb2 := uniq hfeas (Finset.mem_sdiff.1 hx₂).1 (hmemK k₁)
      exact absurd (n₂ k₁ hb2) d₁
    · exact absurd hx₂ (Finset.mem_sdiff.1 hx₁).2
    · obtain rfl := Finset.mem_singleton.1 hx₂
      have hb1 := uniq hfeas (Finset.mem_sdiff.1 hx₁).1 (hmemK k₂)
      exact absurd (n₁ k₂ hb1) d₂
    · exact uniq hfeas (Finset.mem_sdiff.1 hx₁).1 (Finset.mem_sdiff.1 hx₂).1
  have hcb := core_bound (gadget ϕ T U V W) (hsval T U V W) o hcoreIn Finset.univ
    ⟨Sum.inr (Sum.inr (Sum.inl ())), Finset.mem_univ _⟩ (c3 V o i) (S3 o i) hc0 hcB hcV hdisj
    (fun b x _ _ => ⟨owner x, Finset.mem_univ _, endow_owner T U V W x⟩)
  have hBB : ∑ b, o.p b = ∑ s, o.q s := hfeas.2.2.1
  rw [← hBB, sum_buyers (c3 V o i), sum_buyers o.p] at hcb
  have hG0 : ∑ j : Fin ϕ.m, c3 V o i (Sum.inr j) = 0 := Finset.sum_eq_zero fun j _ => rfl
  have hpG : ∑ j : Fin ϕ.m, o.p (Sum.inr j) ≤ ϕ.numTerms := by
    have h1 : ∑ j : Fin ϕ.m, o.p (Sum.inr j) ≤
        ∑ j : Fin ϕ.m, (gadget ϕ T U V W).bval (Sum.inr j) (o.S (Sum.inr j)) :=
      Finset.sum_le_sum fun j _ => (pay_facts hfeas (Sum.inr j)).2.2
    have h2 := bg_sum_le hfeas i
    have h3 := Finset.card_le_univ (Finset.univ.filter fun l : Fin ϕ.numTerms =>
      ∃ j, Fpf l ⊆ o.S (Sum.inr j))
    rw [Fintype.card_fin] at h3
    have h4 : (((Finset.univ.filter fun l : Fin ϕ.numTerms =>
        ∃ j, Fpf l ⊆ o.S (Sum.inr j)).card : ℕ) : ℝ) ≤ ϕ.numTerms := by
      exact_mod_cast h3
    linarith
  have hk6 : ∀ k : Fin ϕ.n, k ≠ i →
      o.p (Sum.inl (BKind.K, k)) + o.p (Sum.inl (BKind.M, k)) +
        o.p (Sum.inl (BKind.chi1, k)) + o.p (Sum.inl (BKind.chi2, k)) +
        o.p (Sum.inl (BKind.lam1, k)) + o.p (Sum.inl (BKind.lam2, k)) - T ≤
      c3 V o i (Sum.inl (BKind.K, k)) + c3 V o i (Sum.inl (BKind.M, k)) +
        c3 V o i (Sum.inl (BKind.chi1, k)) + c3 V o i (Sum.inl (BKind.chi2, k)) +
        c3 V o i (Sum.inl (BKind.lam1, k)) + c3 V o i (Sum.inl (BKind.lam2, k)) := by
    intro k hki
    have eK : c3 V o i (Sum.inl (BKind.K, k)) =
        if Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) then
          o.p (Sum.inl (BKind.K, k)) else 0 := rfl
    have eM : c3 V o i (Sum.inl (BKind.M, k)) = o.p (Sum.inl (BKind.M, k)) := if_neg hki
    have eL1 : c3 V o i (Sum.inl (BKind.lam1, k)) = o.p (Sum.inl (BKind.lam1, k)) :=
      if_neg hki
    have eL2 : c3 V o i (Sum.inl (BKind.lam2, k)) = o.p (Sum.inl (BKind.lam2, k)) :=
      if_neg hki
    have eC1 : c3 V o i (Sum.inl (BKind.chi1, k)) =
        if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧ idleK o k = BKind.chi1 then V
        else o.p (Sum.inl (BKind.chi1, k)) := by
      show (if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧ idleK o k = BKind.chi1 then V
        else if k = i then 0 else o.p (Sum.inl (BKind.chi1, k))) = _
      rw [if_neg hki]
    have eC2 : c3 V o i (Sum.inl (BKind.chi2, k)) =
        if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧ idleK o k = BKind.chi2 then V
        else o.p (Sum.inl (BKind.chi2, k)) := by
      show (if ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧ idleK o k = BKind.chi2 then V
        else if k = i then 0 else o.p (Sum.inl (BKind.chi2, k))) = _
      rw [if_neg hki]
    rw [eK, eM, eC1, eC2, eL1, eL2]
    by_cases hd : Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i)
    · have n1 : ¬ (¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
          idleK o k = BKind.chi1) := fun h => h.1 hd
      have n2 : ¬ (¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
          idleK o k = BKind.chi2) := fun h => h.1 hd
      rw [if_pos hd, if_neg n1, if_neg n2]
      linarith
    · rw [if_neg hd]
      have hpK := (pay_facts hfeas (Sum.inl (BKind.K, k))).2.1
      have hbK : (gadget ϕ T U V W).budget (Sum.inl (BKind.K, k)) = V + T := rfl
      have hv := idle_val hfeas k (hmemK k)
      have hpi := (pay_facts hfeas (Sum.inl (idleK o k, k))).2.2
      rcases idleK_cases o k with hI | hI
      · have c1 : ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
            idleK o k = BKind.chi1 := ⟨hd, hI⟩
        have c2 : ¬ (¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
            idleK o k = BKind.chi2) := by
          rintro ⟨_, h⟩
          rw [hI] at h
          exact absurd h (by decide)
        rw [if_pos c1, if_neg c2]
        rw [hI] at hv hpi
        linarith
      · have c1 : ¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
            idleK o k = BKind.chi2 := ⟨hd, hI⟩
        have c2 : ¬ (¬ Disjoint (o.S (Sum.inl (BKind.K, k))) (NN o i) ∧
            idleK o k = BKind.chi1) := by
          rintro ⟨_, h⟩
          rw [hI] at h
          exact absurd h (by decide)
        rw [if_pos c1, if_neg c2]
        rw [hI] at hv hpi
        linarith
  have hk6i :
      o.p (Sum.inl (BKind.K, i)) + o.p (Sum.inl (BKind.M, i)) +
        o.p (Sum.inl (BKind.chi1, i)) + o.p (Sum.inl (BKind.chi2, i)) +
        o.p (Sum.inl (BKind.lam1, i)) + o.p (Sum.inl (BKind.lam2, i)) - T + (V - 2 * U) ≤
      c3 V o i (Sum.inl (BKind.K, i)) + c3 V o i (Sum.inl (BKind.M, i)) +
        c3 V o i (Sum.inl (BKind.chi1, i)) + c3 V o i (Sum.inl (BKind.chi2, i)) +
        c3 V o i (Sum.inl (BKind.lam1, i)) + c3 V o i (Sum.inl (BKind.lam2, i)) := by
    have eK : c3 V o i (Sum.inl (BKind.K, i)) =
        if Disjoint (o.S (Sum.inl (BKind.K, i))) (NN o i) then
          o.p (Sum.inl (BKind.K, i)) else 0 := rfl
    have eM : c3 V o i (Sum.inl (BKind.M, i)) = 2 * V := if_pos (rfl : i = i)
    have eL1 : c3 V o i (Sum.inl (BKind.lam1, i)) = 0 := if_pos (rfl : i = i)
    have eL2 : c3 V o i (Sum.inl (BKind.lam2, i)) = 0 := if_pos (rfl : i = i)
    have eC1 : c3 V o i (Sum.inl (BKind.chi1, i)) =
        if ¬ Disjoint (o.S (Sum.inl (BKind.K, i))) (NN o i) ∧ idleK o i = BKind.chi1 then V
        else 0 := by
      show (if ¬ Disjoint (o.S (Sum.inl (BKind.K, i))) (NN o i) ∧ idleK o i = BKind.chi1 then V
        else if i = i then 0 else o.p (Sum.inl (BKind.chi1, i))) = _
      rw [if_pos (rfl : i = i)]
    have eC2 : c3 V o i (Sum.inl (BKind.chi2, i)) =
        if ¬ Disjoint (o.S (Sum.inl (BKind.K, i))) (NN o i) ∧ idleK o i = BKind.chi2 then V
        else 0 := by
      show (if ¬ Disjoint (o.S (Sum.inl (BKind.K, i))) (NN o i) ∧ idleK o i = BKind.chi2 then V
        else if i = i then 0 else o.p (Sum.inl (BKind.chi2, i))) = _
      rw [if_pos (rfl : i = i)]
    rw [eK, eM, eC1, eC2, eL1, eL2, hpM0]
    have hl1 := (pay_facts hfeas (Sum.inl (BKind.lam1, i))).2.1
    have hl2 := (pay_facts hfeas (Sum.inl (BKind.lam2, i))).2.1
    have hb1 : (gadget ϕ T U V W).budget (Sum.inl (BKind.lam1, i)) = U := rfl
    have hb2 : (gadget ϕ T U V W).budget (Sum.inl (BKind.lam2, i)) = U := rfl
    have hc1 := (pay_facts hfeas (Sum.inl (BKind.chi1, i))).2.1
    have hc2 := (pay_facts hfeas (Sum.inl (BKind.chi2, i))).2.1
    have hbc1 : (gadget ϕ T U V W).budget (Sum.inl (BKind.chi1, i)) = V := rfl
    have hbc2 : (gadget ϕ T U V W).budget (Sum.inl (BKind.chi2, i)) = V := rfl
    have hpc1 := (pay_facts hfeas (Sum.inl (BKind.chi1, i))).1
    have hpc2 := (pay_facts hfeas (Sum.inl (BKind.chi2, i))).1
    by_cases hd : Disjoint (o.S (Sum.inl (BKind.K, i))) (NN o i)
    · have n1 : ¬ (¬ Disjoint (o.S (Sum.inl (BKind.K, i))) (NN o i) ∧
          idleK o i = BKind.chi1) := fun h => h.1 hd
      have n2 : ¬ (¬ Disjoint (o.S (Sum.inl (BKind.K, i))) (NN o i) ∧
          idleK o i = BKind.chi2) := fun h => h.1 hd
      rw [if_pos hd, if_neg n1, if_neg n2]
      have := chi_pay hfeas i (hmemK i)
      linarith
    · rw [if_neg hd]
      have hpK := (pay_facts hfeas (Sum.inl (BKind.K, i))).2.1
      have hbK : (gadget ϕ T U V W).budget (Sum.inl (BKind.K, i)) = V + T := rfl
      have hv := idle_val hfeas i (hmemK i)
      have hpi := (pay_facts hfeas (Sum.inl (idleK o i, i))).2.2
      rcases idleK_cases o i with hI | hI
      · have c1 : ¬ Disjoint (o.S (Sum.inl (BKind.K, i))) (NN o i) ∧
            idleK o i = BKind.chi1 := ⟨hd, hI⟩
        have c2 : ¬ (¬ Disjoint (o.S (Sum.inl (BKind.K, i))) (NN o i) ∧
            idleK o i = BKind.chi2) := by
          rintro ⟨_, h⟩
          rw [hI] at h
          exact absurd h (by decide)
        rw [if_pos c1, if_neg c2]
        rw [hI] at hv hpi
        linarith
      · have c1 : ¬ Disjoint (o.S (Sum.inl (BKind.K, i))) (NN o i) ∧
            idleK o i = BKind.chi2 := ⟨hd, hI⟩
        have c2 : ¬ (¬ Disjoint (o.S (Sum.inl (BKind.K, i))) (NN o i) ∧
            idleK o i = BKind.chi1) := by
          rintro ⟨_, h⟩
          rw [hI] at h
          exact absurd h (by decide)
        rw [if_pos c1, if_neg c2]
        rw [hI] at hv hpi
        linarith
  have hsum : ∑ k : Fin ϕ.n, (o.p (Sum.inl (BKind.K, k)) + o.p (Sum.inl (BKind.M, k)) +
        o.p (Sum.inl (BKind.chi1, k)) + o.p (Sum.inl (BKind.chi2, k)) +
        o.p (Sum.inl (BKind.lam1, k)) + o.p (Sum.inl (BKind.lam2, k))) -
        (ϕ.n : ℝ) * T + (V - 2 * U) ≤
      ∑ k : Fin ϕ.n, (c3 V o i (Sum.inl (BKind.K, k)) + c3 V o i (Sum.inl (BKind.M, k)) +
        c3 V o i (Sum.inl (BKind.chi1, k)) + c3 V o i (Sum.inl (BKind.chi2, k)) +
        c3 V o i (Sum.inl (BKind.lam1, k)) + c3 V o i (Sum.inl (BKind.lam2, k))) := by
    have hdn : ∀ k ∈ (Finset.univ : Finset (Fin ϕ.n)), (0 : ℝ) ≤
        (c3 V o i (Sum.inl (BKind.K, k)) + c3 V o i (Sum.inl (BKind.M, k)) +
          c3 V o i (Sum.inl (BKind.chi1, k)) + c3 V o i (Sum.inl (BKind.chi2, k)) +
          c3 V o i (Sum.inl (BKind.lam1, k)) + c3 V o i (Sum.inl (BKind.lam2, k))) -
        (o.p (Sum.inl (BKind.K, k)) + o.p (Sum.inl (BKind.M, k)) +
          o.p (Sum.inl (BKind.chi1, k)) + o.p (Sum.inl (BKind.chi2, k)) +
          o.p (Sum.inl (BKind.lam1, k)) + o.p (Sum.inl (BKind.lam2, k)) - T) := by
      intro k _
      by_cases hki : k = i
      · subst hki
        have h6 := hk6i
        have h7 : 0 ≤ V - 2 * U := by linarith
        linarith
      · have h6 := hk6 k hki
        linarith
    have hsingle := Finset.single_le_sum hdn (Finset.mem_univ i)
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsingle
    linarith
  have harith : (ϕ.n : ℝ) * T + ϕ.numTerms < V - 2 * U := by linarith
  linarith

end Aux_BCE

theorem solution (ϕ : BudgetCoreExchange.DNF) (T U V W : ℝ)
    (hA : BudgetCoreExchange.Admissible ϕ T U V W)
    (o : BudgetCoreExchange.Outcome (BudgetCoreExchange.GBuyer ϕ)
      (BudgetCoreExchange.GSeller ϕ) (BudgetCoreExchange.GItem ϕ))
    (ho : BudgetCoreExchange.IsNWEquilibrium ϕ T U V W o)
    (i : Fin ϕ.n) :
    BudgetCoreExchange.Gadget.Mb i ⊆ o.S (BudgetCoreExchange.Gadget.BM i) ∨
      BudgetCoreExchange.Gadget.Mbar i ⊆ o.S (BudgetCoreExchange.Gadget.BM i) :=
  Aux_BCE.lemma3_main ϕ T U V W hA o ho i

-- Prove2me | solution 1 for BudgetCoreExchange.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:52:17.230038+00:00
-- url     : https://prove2.me/submissions/1b2596f4-506d-4556-b4ad-ac6da288dac6

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

theorem solution (ϕ : BudgetCoreExchange.DNF) (T U V W : ℝ)
    (hA : BudgetCoreExchange.Admissible ϕ T U V W)
    (o : BudgetCoreExchange.Outcome (BudgetCoreExchange.GBuyer ϕ)
      (BudgetCoreExchange.GSeller ϕ) (BudgetCoreExchange.GItem ϕ))
    (ho : BudgetCoreExchange.IsNWEquilibrium ϕ T U V W o)
    (i : Fin ϕ.n) :
    ∃ l : Fin ϕ.numTerms,
      BudgetCoreExchange.Gadget.Kb l i ⊆ o.S (BudgetCoreExchange.Gadget.BK i) ∨
        BudgetCoreExchange.Gadget.Kbar l i ⊆ o.S (BudgetCoreExchange.Gadget.BK i) :=
  Aux_BCE1.main ϕ T U V W hA o ho i

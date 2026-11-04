-- Prove2me | solution 1 for ClearingUnique.Cycles.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T07:24:32.037281+00:00
-- url     : https://prove2.me/submissions/f6369c8a-59a6-4e11-8c79-230b4e702441

import Mathlib
import Definitions.Def_ClearingUnique_Cycles_Model

open ClearingUnique.Cycles

set_option linter.unusedSectionVars false

namespace CU45Aux

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma d_nonneg {N : FinNetwork I} (hN : N.Standing) (i : I) {E : ℝ} (hE : 0 ≤ E) (j : I) :
    0 ≤ N.d i E j := ((hN.2.2.2.1 i E hE).1 j).1

lemma d_le_L {N : FinNetwork I} (hN : N.Standing) (i : I) {E : ℝ} (hE : 0 ≤ E) (j : I) :
    N.d i E j ≤ N.L i j := ((hN.2.2.2.1 i E hE).1 j).2

lemma d_sum {N : FinNetwork I} (hN : N.Standing) (i : I) {E : ℝ} (hE : 0 ≤ E) :
    ∑ j, N.d i E j = min E (N.Lbar i) := (hN.2.2.2.1 i E hE).2

lemma d_mono {N : FinNetwork I} (hN : N.Standing) (i : I) {E E' : ℝ} (hE : 0 ≤ E)
    (h : E ≤ E') (j : I) : N.d i E j ≤ N.d i E' j := hN.2.2.2.2 i j E E' hE h

lemma Lbar_nonneg {N : FinNetwork I} (hN : N.Standing) (i : I) : 0 ≤ N.Lbar i :=
  Finset.sum_nonneg (fun j _ => hN.2.1 i j)

lemma d_zero {N : FinNetwork I} (hN : N.Standing) (i j : I) : N.d i 0 j = 0 := by
  have h := d_sum hN i (le_refl 0)
  rw [min_eq_left (Lbar_nonneg hN i)] at h
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => d_nonneg hN i (le_refl 0) k)).1 h j
    (Finset.mem_univ _)

lemma row_eq_of_le {N : FinNetwork I} (hN : N.Standing) (i : I) {E E' : ℝ} (hE : 0 ≤ E)
    (hle : E ≤ E') (hm : min E (N.Lbar i) = min E' (N.Lbar i)) (j : I) :
    N.d i E j = N.d i E' j := by
  have hs : ∑ k, N.d i E k = ∑ k, N.d i E' k := by
    rw [d_sum hN i hE, d_sum hN i (hE.trans hle), hm]
  exact (Finset.sum_eq_sum_iff_of_le (fun k _ => d_mono hN i hE hle k)).1 hs j (Finset.mem_univ _)

lemma row_eq {N : FinNetwork I} (hN : N.Standing) (i : I) {E E' : ℝ} (hE : 0 ≤ E)
    (hE' : 0 ≤ E') (hm : min E (N.Lbar i) = min E' (N.Lbar i)) (j : I) :
    N.d i E j = N.d i E' j := by
  rcases le_total E E' with h | h
  · exact row_eq_of_le hN i hE h hm j
  · exact (row_eq_of_le hN i hE' h hm.symm j).symm

lemma assetValue_nonneg {N : FinNetwork I} (hN : N.Standing) {P : I → I → ℝ}
    (hP : ∀ i j, 0 ≤ P i j) (i : I) : 0 ≤ assetValue N P i :=
  add_nonneg (hN.1 i) (Finset.sum_nonneg (fun j _ => hP j i))

/-- Theorem 3.1 -/
theorem thm31 {N : FinNetwork I} (hN : N.Standing) (P : I → I → ℝ) (hP : InM P) :
    IsClearing N P ↔ ∀ i j, P i j = N.d i (assetValue N P i) j := by
  constructor
  · rintro ⟨⟨-, hfeas⟩, hlim, hprio⟩ i
    obtain ⟨E, hE0, hrow⟩ := hfeas i
    have ha := assetValue_nonneg hN hP.1 i
    have hs : ∑ j, P i j = min E (N.Lbar i) := by
      simp_rw [hrow]; exact d_sum hN i hE0
    have hl := hlim i
    unfold equity at hl
    have hsa : ∑ j, P i j ≤ assetValue N P i := by linarith
    have hsL : ∑ j, P i j ≤ N.Lbar i := by rw [hs]; exact min_le_right _ _
    have key : min E (N.Lbar i) = min (assetValue N P i) (N.Lbar i) := by
      by_contra hne
      have hlt : ∑ j, P i j < min (assetValue N P i) (N.Lbar i) := by
        rcases lt_or_eq_of_le (le_min hsa hsL) with h | h
        · exact h
        · exact absurd (hs ▸ h) hne
      have hrl : RowLt P N.L i := by
        refine ⟨fun j => (hrow j).symm ▸ d_le_L hN i hE0 j, ?_⟩
        by_contra hc
        simp only [not_exists, not_lt] at hc
        have : N.Lbar i ≤ ∑ j, P i j := Finset.sum_le_sum (fun j _ => hc j)
        have := min_le_right (assetValue N P i) (N.Lbar i)
        linarith
      have he := hprio i hrl
      unfold equity at he
      have := min_le_left (assetValue N P i) (N.Lbar i)
      linarith
    intro j
    rw [hrow j]
    exact row_eq hN i hE0 ha key j
  · intro hfix
    have hs : ∀ i, ∑ j, P i j = min (assetValue N P i) (N.Lbar i) := by
      intro i
      simp_rw [hfix i]
      exact d_sum hN i (assetValue_nonneg hN hP.1 i)
    refine ⟨⟨hP, fun i => ⟨assetValue N P i, assetValue_nonneg hN hP.1 i, hfix i⟩⟩, ?_, ?_⟩
    · intro i
      unfold equity
      rw [hs i]
      have := min_le_left (assetValue N P i) (N.Lbar i)
      linarith
    · rintro i ⟨hle, j, hj⟩
      have hlt : ∑ j, P i j < N.Lbar i :=
        Finset.sum_lt_sum (fun k _ => hle k) ⟨j, Finset.mem_univ _, hj⟩
      unfold equity
      rw [hs i] at hlt ⊢
      have : min (assetValue N P i) (N.Lbar i) = assetValue N P i := by
        rcases min_choice (assetValue N P i) (N.Lbar i) with h | h
        · exact h
        · rw [h] at hlt; exact absurd hlt (lt_irrefl _)
      rw [this]; ring

lemma mem_comp {N : FinNetwork I} (i x : I) :
    x ∈ N.comp i ↔ x = i ∨ (N.Reach i x ∧ N.Reach x i) := by
  simp [FinNetwork.comp]

lemma cut_sum (R : Finset I) (M : I → I → ℝ) :
    ∑ x ∈ R, (∑ y, M y x - ∑ y, M x y) = ∑ x ∈ R, ∑ y ∈ Rᶜ, (M y x - M x y) := by
  have h1 : ∀ x, ∑ y, M y x = ∑ y ∈ R, M y x + ∑ y ∈ Rᶜ, M y x :=
    fun x => (Finset.sum_add_sum_compl R _).symm
  have h2 : ∀ x, ∑ y, M x y = ∑ y ∈ R, M x y + ∑ y ∈ Rᶜ, M x y :=
    fun x => (Finset.sum_add_sum_compl R _).symm
  simp_rw [h1, h2, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := R) (t := R) (f := fun x y => M y x)]
  ring

theorem main {N : FinNetwork I} (hN : N.Standing)
    (h1 : ∀ i, N.Cyclical i → N.NoSuccessors (N.comp i) → 0 < ∑ j ∈ N.comp i, N.z j)
    (h2 : ∀ i, N.Cyclical i → 0 < N.z i → PositiveMonotonic N i)
    (h3 : ∀ i, N.Cyclical i → N.z i = 0 → StrictlyMonotonic N i)
    (P Q : I → I → ℝ) (hP0 : ∀ i j, 0 ≤ P i j)
    (hP : ∀ i j, P i j = N.d i (assetValue N P i) j)
    (hQ : ∀ i j, Q i j = N.d i (assetValue N Q i) j)
    (hPQ : ∀ i j, P i j ≤ Q i j) : P = Q := by
  classical
  have hQ0 : ∀ i j, 0 ≤ Q i j := fun i j => (hP0 i j).trans (hPQ i j)
  have haP := assetValue_nonneg hN hP0
  have haQ := assetValue_nonneg hN hQ0
  have haPQ : ∀ i, assetValue N P i ≤ assetValue N Q i := fun i =>
    add_le_add le_rfl (Finset.sum_le_sum (fun j _ => hPQ j i))
  have hQL : ∀ i j, Q i j ≤ N.L i j := fun i j => (hQ i j).symm ▸ d_le_L hN i (haQ i) j
  have hsP : ∀ i, ∑ j, P i j = min (assetValue N P i) (N.Lbar i) := fun i => by
    simp_rw [hP i]; exact d_sum hN i (haP i)
  have hsQ : ∀ i, ∑ j, Q i j = min (assetValue N Q i) (N.Lbar i) := fun i => by
    simp_rw [hQ i]; exact d_sum hN i (haQ i)
  have heP : ∀ i, equity N P i = assetValue N P i - min (assetValue N P i) (N.Lbar i) :=
    fun i => by unfold equity; rw [hsP i]
  have heQ : ∀ i, equity N Q i = assetValue N Q i - min (assetValue N Q i) (N.Lbar i) :=
    fun i => by unfold equity; rw [hsQ i]
  have hsumE : ∀ R : I → I → ℝ, ∑ i, equity N R i = ∑ i, N.z i := by
    intro R; unfold equity assetValue
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_comm (f := fun i j => R j i)]
    ring
  have heq : ∀ i, equity N P i = equity N Q i := by
    have hle : ∀ i, equity N P i ≤ equity N Q i := by
      intro i; rw [heP, heQ]
      have := haPQ i
      rcases le_total (assetValue N P i) (N.Lbar i) with h | h <;>
      rcases le_total (assetValue N Q i) (N.Lbar i) with h' | h' <;>
      simp only [min_eq_left, min_eq_right, h, h'] <;> linarith
    have hs : ∑ i, equity N P i = ∑ i, equity N Q i := by rw [hsumE, hsumE]
    intro i
    exact (Finset.sum_eq_sum_iff_of_le (fun k _ => hle k)).1 hs i (Finset.mem_univ _)
  set D : I → Prop := fun i => ∃ j, P i j ≠ Q i j with hD
  have hDfacts : ∀ i, D i → assetValue N P i < assetValue N Q i ∧
      assetValue N Q i ≤ N.Lbar i := by
    rintro i ⟨j, hj⟩
    have hm : min (assetValue N P i) (N.Lbar i) ≠ min (assetValue N Q i) (N.Lbar i) := by
      intro hm; apply hj; rw [hP i j, hQ i j]; exact row_eq hN i (haP i) (haQ i) hm j
    have hlt : min (assetValue N P i) (N.Lbar i) < min (assetValue N Q i) (N.Lbar i) :=
      lt_of_le_of_ne (min_le_min (haPQ i) le_rfl) hm
    have hPL : assetValue N P i < N.Lbar i := by
      by_contra hc
      rw [min_eq_right (not_lt.1 hc)] at hlt
      exact absurd hlt (not_lt.2 (min_le_right _ _))
    have hPQ' : assetValue N P i < assetValue N Q i := by
      by_contra hc
      exact absurd hlt (not_lt.2 (min_le_min (not_lt.1 hc) le_rfl))
    have heP0 : equity N P i = 0 := by rw [heP, min_eq_left hPL.le]; ring
    have heQ0 : equity N Q i = 0 := (heq i) ▸ heP0
    rw [heQ] at heQ0
    refine ⟨hPQ', ?_⟩
    by_contra hc
    rw [min_eq_right (not_le.1 hc).le] at heQ0
    linarith [not_le.1 hc]
  have hin : ∀ x, ∑ y, (Q y x - P y x) = assetValue N Q x - assetValue N P x := by
    intro x; unfold assetValue; rw [Finset.sum_sub_distrib]; ring
  have hout : ∀ x, ∑ y, (Q x y - P x y) = assetValue N Q x - assetValue N P x := by
    intro x; have := heq x; unfold equity at this; rw [Finset.sum_sub_distrib]; linarith
  have hinD : ∀ x, 0 < ∑ y, (Q y x - P y x) → D x := by
    intro x hx; rw [hin, ← hout] at hx
    obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx.ne'
    exact ⟨y, fun h => hy (by rw [h]; ring)⟩
  have hinD' : ∀ i x, 0 < Q i x - P i x → D x := by
    intro i x h; apply hinD
    exact lt_of_lt_of_le h (Finset.single_le_sum (f := fun y => Q y x - P y x)
      (fun y _ => sub_nonneg.2 (hPQ y x)) (Finset.mem_univ i))
  have hstep_pos : ∀ i j, D i → PositiveMonotonic N i → 0 < Q i j → 0 < Q i j - P i j := by
    intro i j hDi hpm hq
    obtain ⟨hlt, hle⟩ := hDfacts i hDi
    have hL : 0 < N.L i j := lt_of_lt_of_le hq (hQL i j)
    by_cases ha : aLow N i j ≤ assetValue N P i
    · have := hpm j hL _ _ (haP i) ha hlt hle
      rw [hP i j, hQ i j]; linarith
    · have ha' : assetValue N P i < sSup {E : ℝ | 0 ≤ E ∧ N.d i E j = 0} := not_le.1 ha
      have hne : ({E : ℝ | 0 ≤ E ∧ N.d i E j = 0}).Nonempty := ⟨0, le_refl 0, d_zero hN i j⟩
      obtain ⟨E, ⟨-, hEz⟩, hE⟩ := exists_lt_of_lt_csSup hne ha'
      have : P i j ≤ 0 := by rw [hP i j, ← hEz]; exact d_mono hN i (haP i) hE.le j
      linarith
  have hstep_strict : ∀ i j, D i → StrictlyMonotonic N i → 0 < N.L i j →
      0 < Q i j - P i j := by
    intro i j hDi hsm hL
    obtain ⟨hlt, hle⟩ := hDfacts i hDi
    have := hsm j hL _ _ (haP i) hlt hle
    rw [hP i j, hQ i j]; linarith
  have hLpos : ∀ a b, 0 < Q a b - P a b → 0 < N.L a b := fun a b h => by
    have := hP0 a b; have := hQL a b; linarith
  have hcyc : ∀ i, D i → N.Cyclical i := by
    intro i hDi
    obtain ⟨j, hj⟩ := hDi
    have hΔ : 0 < Q i j - P i j := by
      have : P i j < Q i j := lt_of_le_of_ne (hPQ i j) hj
      linarith
    let R : Finset I := Finset.univ.filter
      (fun x => x = j ∨ Relation.TransGen (fun a b => 0 < Q a b - P a b) j x)
    have hcut := cut_sum R (fun a b => Q a b - P a b)
    have hzero : ∑ x ∈ R, (∑ y, (Q y x - P y x) - ∑ y, (Q x y - P x y)) = 0 :=
      Finset.sum_eq_zero (fun x _ => by rw [hin, hout]; ring)
    have hclosed : ∀ x ∈ R, ∀ y ∉ R, Q x y - P x y = 0 := by
      intro x hx y hy
      by_contra hne
      have hpos : 0 < Q x y - P x y := lt_of_le_of_ne (sub_nonneg.2 (hPQ x y)) (Ne.symm hne)
      apply hy
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      right
      rcases hx with rfl | hx
      · exact Relation.TransGen.single hpos
      · exact Relation.TransGen.tail hx hpos
    have hrhs : ∑ x ∈ R, ∑ y ∈ Rᶜ, (Q y x - P y x) = 0 := by
      rw [← hzero, hcut]
      apply Finset.sum_congr rfl; intro x hx; apply Finset.sum_congr rfl; intro y hy
      rw [hclosed x hx y (Finset.mem_compl.1 hy)]; ring
    have hiR : i ∈ R := by
      by_contra hiR
      have hjR : j ∈ R := by simp [R]
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Finset.sum_nonneg
        (fun y _ => sub_nonneg.2 (hPQ y x)))).1 hrhs j hjR
      have h00 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sub_nonneg.2 (hPQ y j))).1 h0 i
        (Finset.mem_compl.2 hiR)
      linarith
    have hij : i ≠ j := by
      rintro rfl
      have := hLpos i i hΔ; rw [hN.2.2.1 i] at this; exact lt_irrefl _ this
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hiR
    rcases hiR with hiR | hiR
    · exact absurd hiR hij
    have hji : N.Reach j i := Relation.TransGen.mono (fun a b h => hLpos a b h) _ _ hiR
    have hij' : N.Reach i j := Relation.TransGen.single (hLpos i j hΔ)
    have hsub : ({i, j} : Finset I) ⊆ N.comp i := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [mem_comp]
      rcases hx with rfl | rfl
      · left; rfl
      · right; exact ⟨hij', hji⟩
    unfold FinNetwork.Cyclical
    calc 2 = ({i, j} : Finset I).card := (Finset.card_pair hij).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hpm : ∀ i, D i → PositiveMonotonic N i := by
    intro i hDi
    rcases lt_or_eq_of_le (hN.1 i) with hz | hz
    · exact h2 i (hcyc i hDi) hz
    · have := h3 i (hcyc i hDi) hz.symm
      intro j hL E E' hE _ hlt hle; exact this j hL E E' hE hlt hle
  have hDQ : ∀ i j, D i → 0 < Q i j → D j := fun i j hDi hq =>
    hinD' i j (hstep_pos i j hDi (hpm i hDi) hq)
  let DS : Finset I := Finset.univ.filter D
  have hzD : ∀ x, D x → N.z x = 0 := by
    have hcut := cut_sum DS Q
    have heq0 : ∑ x ∈ DS, equity N Q x = 0 := Finset.sum_eq_zero (fun x hx => by
      have hDx : D x := (Finset.mem_filter.1 hx).2
      obtain ⟨-, hle⟩ := hDfacts x hDx
      rw [heQ, min_eq_left hle]; ring)
    have hexp : ∑ x ∈ DS, equity N Q x =
        ∑ x ∈ DS, N.z x + ∑ x ∈ DS, (∑ y, Q y x - ∑ y, Q x y) := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro x _
      unfold equity assetValue; ring
    have hcl : ∀ x ∈ DS, ∀ y ∈ DSᶜ, Q x y = 0 := by
      intro x hx y hy
      by_contra hne
      have hq : 0 < Q x y := lt_of_le_of_ne (hQ0 x y) (Ne.symm hne)
      have := hDQ x y (Finset.mem_filter.1 hx).2 hq
      exact (Finset.mem_compl.1 hy) (Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩)
    have hnn : 0 ≤ ∑ x ∈ DS, (∑ y, Q y x - ∑ y, Q x y) := by
      rw [hcut]; apply Finset.sum_nonneg; intro x hx; apply Finset.sum_nonneg; intro y hy
      rw [hcl x hx y hy, sub_zero]; exact hQ0 y x
    have hz0 : ∑ x ∈ DS, N.z x = 0 := by
      have : 0 ≤ ∑ x ∈ DS, N.z x := Finset.sum_nonneg (fun x _ => hN.1 x)
      linarith
    intro x hx
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hN.1 x)).1 hz0 x
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩)
  have hDL : ∀ i j, D i → 0 < N.L i j → D j := fun i j hDi hL =>
    hinD' i j (hstep_strict i j hDi (h3 i (hcyc i hDi) (hzD i hDi)) hL)
  have hDR : ∀ i j, N.Reach i j → D i → D j := by
    intro i j h
    induction h with
    | single h => exact fun hDi => hDL _ _ hDi h
    | tail _ h ih => exact fun hDi => hDL _ _ (ih hDi) h
  by_contra hne
  have hex : DS.Nonempty := by
    by_contra hno
    apply hne
    funext i j
    by_contra h
    exact hno ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨j, h⟩⟩⟩
  let reachSet : I → Finset I := fun x => Finset.univ.filter (fun y => N.Reach x y)
  obtain ⟨i, hiD, hmin⟩ := Finset.exists_min_image DS (fun x => (reachSet x).card) hex
  have hDi : D i := (Finset.mem_filter.1 hiD).2
  have hcy := hcyc i hDi
  have hii : N.Reach i i := by
    obtain ⟨k, hk, hki⟩ := Finset.exists_mem_ne hcy i
    rcases (mem_comp i k).1 hk with h | ⟨h1', h2'⟩
    · exact absurd h hki
    · exact h1'.trans h2'
  have hNS : N.NoSuccessors (N.comp i) := by
    intro a ha b hab
    have hib : N.Reach i b := by
      rcases (mem_comp i a).1 ha with h | ⟨hia, -⟩
      · subst h; exact Relation.TransGen.single hab
      · exact hia.tail hab
    have hDb : D b := hDR i b hib hDi
    have hsub : reachSet b ⊆ reachSet i := by
      intro y hy
      simp only [reachSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact hib.trans hy
    have hcard := hmin b (Finset.mem_filter.2 ⟨Finset.mem_univ _, hDb⟩)
    have heqs := Finset.eq_of_subset_of_card_le hsub hcard
    have hiin : i ∈ reachSet i := by
      simp only [reachSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact hii
    rw [← heqs] at hiin
    simp only [reachSet, Finset.mem_filter, Finset.mem_univ, true_and] at hiin
    exact (mem_comp i b).2 (Or.inr ⟨hib, hiin⟩)
  have hpos := h1 i hcy hNS
  have : ∑ j ∈ N.comp i, N.z j = 0 := Finset.sum_eq_zero (fun j hj => by
    rcases (mem_comp i j).1 hj with h | ⟨hij, -⟩
    · subst h; exact hzD _ hDi
    · exact hzD j (hDR i j hij hDi))
  linarith

end CU45Aux

namespace CU45Aux

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem fix_props {N : FinNetwork I} (hN : N.Standing)
    (P Q : I → I → ℝ) (hP0 : ∀ i j, 0 ≤ P i j)
    (hP : ∀ i j, P i j = N.d i (assetValue N P i) j)
    (hQ : ∀ i j, Q i j = N.d i (assetValue N Q i) j)
    (hPQ : ∀ i j, P i j ≤ Q i j) :
    (∀ i, equity N P i = equity N Q i) ∧
    (∀ i, (∃ j, P i j ≠ Q i j) → assetValue N P i < assetValue N Q i ∧
      assetValue N Q i ≤ N.Lbar i) ∧
    (∀ i x, 0 < Q i x - P i x → ∃ j, P x j ≠ Q x j) ∧
    (∀ i j, (∃ k, P i k ≠ Q i k) → PositiveMonotonic N i → 0 < Q i j → P i j < Q i j) := by
  classical
  have hQ0 : ∀ i j, 0 ≤ Q i j := fun i j => (hP0 i j).trans (hPQ i j)
  have haP := assetValue_nonneg hN hP0
  have haQ := assetValue_nonneg hN hQ0
  have haPQ : ∀ i, assetValue N P i ≤ assetValue N Q i := fun i =>
    add_le_add le_rfl (Finset.sum_le_sum (fun j _ => hPQ j i))
  have hQL : ∀ i j, Q i j ≤ N.L i j := fun i j => (hQ i j).symm ▸ d_le_L hN i (haQ i) j
  have hsP : ∀ i, ∑ j, P i j = min (assetValue N P i) (N.Lbar i) := fun i => by
    simp_rw [hP i]; exact d_sum hN i (haP i)
  have hsQ : ∀ i, ∑ j, Q i j = min (assetValue N Q i) (N.Lbar i) := fun i => by
    simp_rw [hQ i]; exact d_sum hN i (haQ i)
  have heP : ∀ i, equity N P i = assetValue N P i - min (assetValue N P i) (N.Lbar i) :=
    fun i => by unfold equity; rw [hsP i]
  have heQ : ∀ i, equity N Q i = assetValue N Q i - min (assetValue N Q i) (N.Lbar i) :=
    fun i => by unfold equity; rw [hsQ i]
  have hsumE : ∀ R : I → I → ℝ, ∑ i, equity N R i = ∑ i, N.z i := by
    intro R; unfold equity assetValue
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_comm (f := fun i j => R j i)]
    ring
  have heq : ∀ i, equity N P i = equity N Q i := by
    have hle : ∀ i, equity N P i ≤ equity N Q i := by
      intro i; rw [heP, heQ]
      have := haPQ i
      rcases le_total (assetValue N P i) (N.Lbar i) with h | h <;>
      rcases le_total (assetValue N Q i) (N.Lbar i) with h' | h' <;>
      simp only [min_eq_left, min_eq_right, h, h'] <;> linarith
    have hs : ∑ i, equity N P i = ∑ i, equity N Q i := by rw [hsumE, hsumE]
    intro i
    exact (Finset.sum_eq_sum_iff_of_le (fun k _ => hle k)).1 hs i (Finset.mem_univ _)
  set D : I → Prop := fun i => ∃ j, P i j ≠ Q i j with hD
  have hDfacts : ∀ i, D i → assetValue N P i < assetValue N Q i ∧
      assetValue N Q i ≤ N.Lbar i := by
    rintro i ⟨j, hj⟩
    have hm : min (assetValue N P i) (N.Lbar i) ≠ min (assetValue N Q i) (N.Lbar i) := by
      intro hm; apply hj; rw [hP i j, hQ i j]; exact row_eq hN i (haP i) (haQ i) hm j
    have hlt : min (assetValue N P i) (N.Lbar i) < min (assetValue N Q i) (N.Lbar i) :=
      lt_of_le_of_ne (min_le_min (haPQ i) le_rfl) hm
    have hPL : assetValue N P i < N.Lbar i := by
      by_contra hc
      rw [min_eq_right (not_lt.1 hc)] at hlt
      exact absurd hlt (not_lt.2 (min_le_right _ _))
    have hPQ' : assetValue N P i < assetValue N Q i := by
      by_contra hc
      exact absurd hlt (not_lt.2 (min_le_min (not_lt.1 hc) le_rfl))
    have heP0 : equity N P i = 0 := by rw [heP, min_eq_left hPL.le]; ring
    have heQ0 : equity N Q i = 0 := (heq i) ▸ heP0
    rw [heQ] at heQ0
    refine ⟨hPQ', ?_⟩
    by_contra hc
    rw [min_eq_right (not_le.1 hc).le] at heQ0
    linarith [not_le.1 hc]
  have hin : ∀ x, ∑ y, (Q y x - P y x) = assetValue N Q x - assetValue N P x := by
    intro x; unfold assetValue; rw [Finset.sum_sub_distrib]; ring
  have hout : ∀ x, ∑ y, (Q x y - P x y) = assetValue N Q x - assetValue N P x := by
    intro x; have := heq x; unfold equity at this; rw [Finset.sum_sub_distrib]; linarith
  have hinD : ∀ x, 0 < ∑ y, (Q y x - P y x) → D x := by
    intro x hx; rw [hin, ← hout] at hx
    obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx.ne'
    exact ⟨y, fun h => hy (by rw [h]; ring)⟩
  have hinD' : ∀ i x, 0 < Q i x - P i x → D x := by
    intro i x h; apply hinD
    exact lt_of_lt_of_le h (Finset.single_le_sum (f := fun y => Q y x - P y x)
      (fun y _ => sub_nonneg.2 (hPQ y x)) (Finset.mem_univ i))
  have hstep_pos : ∀ i j, D i → PositiveMonotonic N i → 0 < Q i j → 0 < Q i j - P i j := by
    intro i j hDi hpm hq
    obtain ⟨hlt, hle⟩ := hDfacts i hDi
    have hL : 0 < N.L i j := lt_of_lt_of_le hq (hQL i j)
    by_cases ha : aLow N i j ≤ assetValue N P i
    · have := hpm j hL _ _ (haP i) ha hlt hle
      rw [hP i j, hQ i j]; linarith
    · have ha' : assetValue N P i < sSup {E : ℝ | 0 ≤ E ∧ N.d i E j = 0} := not_le.1 ha
      have hne : ({E : ℝ | 0 ≤ E ∧ N.d i E j = 0}).Nonempty := ⟨0, le_refl 0, d_zero hN i j⟩
      obtain ⟨E, ⟨-, hEz⟩, hE⟩ := exists_lt_of_lt_csSup hne ha'
      have : P i j ≤ 0 := by rw [hP i j, ← hEz]; exact d_mono hN i (haP i) hE.le j
      linarith
  have hstep_strict : ∀ i j, D i → StrictlyMonotonic N i → 0 < N.L i j →
      0 < Q i j - P i j := by
    intro i j hDi hsm hL
    obtain ⟨hlt, hle⟩ := hDfacts i hDi
    have := hsm j hL _ _ (haP i) hlt hle
    rw [hP i j, hQ i j]; linarith
  refine ⟨heq, hDfacts, hinD', fun i j hDi hpm hq => ?_⟩
  have := hstep_pos i j hDi hpm hq
  linarith

noncomputable def phi {N : FinNetwork I} (hN : N.Standing) :
    Set.Icc (0 : I → I → ℝ) N.L →o Set.Icc (0 : I → I → ℝ) N.L :=
  { toFun := fun P => ⟨fun i j => N.d i (assetValue N P.1 i) j,
      fun i j => d_nonneg hN i (assetValue_nonneg hN (fun a b => P.2.1 a b) i) j,
      fun i j => d_le_L hN i (assetValue_nonneg hN (fun a b => P.2.1 a b) i) j⟩
    monotone' := fun P Q hPQ i j =>
      d_mono hN i (assetValue_nonneg hN (fun a b => P.2.1 a b) i)
        (add_le_add le_rfl (Finset.sum_le_sum fun k _ => hPQ k i)) j }

lemma phi_fix_iff {N : FinNetwork I} (hN : N.Standing) (x : Set.Icc (0 : I → I → ℝ) N.L) :
    phi hN x = x ↔ ∀ i j, x.1 i j = N.d i (assetValue N x.1 i) j := by
  constructor
  · intro h i j
    exact (congrArg (fun R : Set.Icc (0 : I → I → ℝ) N.L => R.1 i j) h).symm
  · intro h
    exact Subtype.ext (funext fun i => funext fun j => (h i j).symm)

lemma clearing_iff_box {N : FinNetwork I} (hN : N.Standing) (R : I → I → ℝ) :
    IsClearing N R ↔ ∃ h : R ∈ Set.Icc (0 : I → I → ℝ) N.L, phi hN ⟨R, h⟩ = ⟨R, h⟩ := by
  constructor
  · intro hR
    have hfix := (thm31 hN R hR.1.1).1 hR
    have hbox : R ∈ Set.Icc (0 : I → I → ℝ) N.L :=
      ⟨fun i j => hR.1.1.1 i j, fun i j => by
        rw [hfix i j]; exact d_le_L hN i (assetValue_nonneg hN hR.1.1.1 i) j⟩
    exact ⟨hbox, (phi_fix_iff hN ⟨R, hbox⟩).2 hfix⟩
  · rintro ⟨hbox, hfix⟩
    have hInM : InM R := ⟨fun i j => hbox.1 i j, fun i => le_antisymm
      (by have := hbox.2 i i; rwa [hN.2.2.1 i] at this) (hbox.1 i i)⟩
    exact (thm31 hN R hInM).2 ((phi_fix_iff hN ⟨R, hbox⟩).1 hfix)

lemma clearing_fix {N : FinNetwork I} (hN : N.Standing) {P : I → I → ℝ}
    (hP : IsClearing N P) :
    (∀ i j, 0 ≤ P i j) ∧ ∀ i j, P i j = N.d i (assetValue N P i) j :=
  ⟨hP.1.1.1, (thm31 hN P hP.1.1).1 hP⟩

lemma exists_least {N : FinNetwork I} (hN : N.Standing) :
    ∃ P0, IsClearing N P0 ∧ ∀ P, IsClearing N P → ∀ i j, P0 i j ≤ P i j := by
  have : Fact ((0 : I → I → ℝ) ≤ N.L) := ⟨fun i j => hN.2.1 i j⟩
  refine ⟨(phi hN).lfp.1, (clearing_iff_box hN _).2 ⟨(phi hN).lfp.2, (phi hN).map_lfp⟩, ?_⟩
  intro P hP
  obtain ⟨hbox, hfix⟩ := (clearing_iff_box hN P).1 hP
  have hle : (phi hN).lfp ≤ ⟨P, hbox⟩ := (phi hN).lfp_le_fixed hfix
  exact fun i j => hle i j

theorem equity_eq {N : FinNetwork I} (hN : N.Standing) (P Q : I → I → ℝ)
    (hP : IsClearing N P) (hQ : IsClearing N Q) : ∀ i, equity N P i = equity N Q i := by
  obtain ⟨P0, h0, hmin⟩ := exists_least hN
  have e1 := (fix_props hN P0 P (clearing_fix hN h0).1 (clearing_fix hN h0).2
    (clearing_fix hN hP).2 (hmin P hP)).1
  have e2 := (fix_props hN P0 Q (clearing_fix hN h0).1 (clearing_fix hN h0).2
    (clearing_fix hN hQ).2 (hmin Q hQ)).1
  intro i; rw [← e1 i, ← e2 i]

end CU45Aux

open ClearingUnique.Cycles CU45Aux in
theorem solution {I : Type*} [Fintype I] [DecidableEq I] (N : FinNetwork I) (hN : N.Standing)
    (Pm Pp : I → I → ℝ)
    (hm : IsLeast {P : I → I → ℝ | IsClearing N P} Pm)
    (hp : IsGreatest {P : I → I → ℝ | IsClearing N P} Pp)
    (i : I) (hrow : RowLt Pm Pp i) :
    equity N Pm i = 0 ∧ equity N Pp i = 0 := by
  have hle : Pm ≤ Pp := hm.2 hp.1
  obtain ⟨heq, hD, -, -⟩ := fix_props hN Pm Pp (clearing_fix hN hm.1).1
    (clearing_fix hN hm.1).2 (clearing_fix hN hp.1).2 (fun i j => hle i j)
  obtain ⟨j, hj⟩ := hrow.2
  obtain ⟨-, hQL⟩ := hD i ⟨j, hj.ne⟩
  have hsQ : ∑ k, Pp i k = min (assetValue N Pp i) (N.Lbar i) := by
    simp_rw [(clearing_fix hN hp.1).2 i]
    exact d_sum hN i (assetValue_nonneg hN (clearing_fix hN hp.1).1 i)
  have h0 : equity N Pp i = 0 := by unfold equity; rw [hsQ, min_eq_left hQL]; ring
  exact ⟨(heq i).trans h0, h0⟩

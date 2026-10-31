-- Prove2me | solution 1 for EndogBudgetAds.Equilibrium.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T16:37:00.584998+00:00
-- url     : https://prove2.me/submissions/14543e3b-4ffd-4bc2-b953-c9f9db59ac6f

import Mathlib
import Definitions.Def_EndogBudgetAds_Equilibrium_Model
import Definitions.Def_EndogBudgetAds_Equilibrium_Proof
open MeasureTheory

namespace EndogLemma6Aux
open EndogBudgetAds.Equilibrium

abbrev Top {m : ℕ} (x : Fin m → ℝ) (k : Fin m) : Prop := EndogBudgetAds.Equilibrium.IsTop x k

lemma le_top2_of_top {m : ℕ} {x : Fin m → ℝ} {k l : Fin m} (hk : Top x k) (hl : l ≠ k) :
    x l ≤ top2 x := by
  unfold top2
  have hmem : (l, k) ∈ (Finset.univ.filter fun p : Fin m × Fin m => p.1 ≠ p.2) := by
    simp [hl]
  rw [dif_pos ⟨_, hmem⟩]
  refine le_trans ?_ (Finset.le_sup' (fun p => min (x p.1) (x p.2)) hmem)
  simp only
  rw [min_eq_left (le_of_lt (hk l hl))]

lemma top2_nonneg_pos {m : ℕ} (x : Fin m → ℝ) (hx : ∀ l, 0 < x l) : 0 ≤ top2 x := by
  unfold top2
  split_ifs with h
  · obtain ⟨p, hp⟩ := h
    exact le_trans (le_min (hx p.1).le (hx p.2).le)
      (Finset.le_sup' (fun p => min (x p.1) (x p.2)) hp)
  · exact le_rfl

/-- If `k` tops `x` and `j` is second, then `top2 x ≤ x j`. -/
lemma top2_le_second {m : ℕ} {x : Fin m → ℝ} {k j : Fin m} (hk : Top x k)
    (hj : IsSecond x j) : top2 x ≤ x j := by
  obtain ⟨l0, hl0j, hlt, hall⟩ := hj
  have hl0k : l0 = k := by
    by_contra h
    by_cases hkj : k = j
    · exact lt_asymm hlt (by rw [← hkj]; exact hk l0 h)
    · exact lt_asymm (hall k (Ne.symm h) hkj) (lt_trans hlt (hk l0 h))
  have hle : ∀ l, l ≠ k → x l ≤ x j := fun l hl => by
    by_cases hlj : l = j
    · rw [hlj]
    · exact le_of_lt (hall l (by rw [hl0k]; exact hl) hlj)
  unfold top2
  split_ifs with h
  · apply Finset.sup'_le
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases h1 : p.1 = k
    · have : p.2 ≠ k := fun h2 => hp (h1.trans h2.symm)
      exact le_trans (min_le_right _ _) (hle _ this)
    · exact le_trans (min_le_left _ _) (hle _ h1)
  · have hjk : j ≠ k := fun h => lt_irrefl _ (by rw [h] at hlt; rw [hl0k] at hlt; exact hlt)
    exfalso; exact h ⟨(j, k), by simp [hjk]⟩

lemma pay_top_eq {m n : ℕ} (b : Fin m → Fin n → ℝ) (i : Fin n) (t : Fin m)
    (ht : Top (fun l => b l i) t) : pay b i t = top2 (fun l => b l i) := by
  unfold pay
  split_ifs with hex
  · apply le_antisymm
    · apply Finset.sup'_le
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      exact le_top2_of_top ht hl.1
    · unfold top2
      split_ifs with h
      · apply Finset.sup'_le
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        by_cases h1 : p.1 = t
        · have h2 : p.2 ≠ t := fun h2 => hp (h1.trans h2.symm)
          exact le_trans (min_le_right _ _) (Finset.le_sup' (fun k => b k i) (by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨h2, le_of_lt (ht _ h2)⟩))
        · exact le_trans (min_le_left _ _) (Finset.le_sup' (fun k => b k i) (by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨h1, le_of_lt (ht _ h1)⟩))
      · exfalso
        obtain ⟨l, hl⟩ := hex
        have hlt : l ≠ t := fun h => lt_irrefl _ (by rw [h] at hl; exact hl)
        exact h ⟨(l, t), by simp [hlt]⟩
  · unfold top2
    rw [dif_neg]
    rintro ⟨p, hp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    apply hex
    by_cases h1 : p.1 = t
    · exact ⟨p.2, ht p.2 (fun h2 => hp (h1.trans h2.symm))⟩
    · exact ⟨p.1, ht p.1 h1⟩

lemma pay_lt_top2 {m n : ℕ} (b : Fin m → Fin n → ℝ) (i : Fin n) (t k : Fin m)
    (ht : Top (fun l => b l i) t) (hkt : k ≠ t) (hpos : ∀ l, 0 < b l i)
    (hnt : ∀ a c, a ≠ c → b a i ≠ b c i) : pay b i k < top2 (fun l => b l i) := by
  have hk2 : b k i ≤ top2 (fun l => b l i) := le_top2_of_top ht hkt
  unfold pay
  split_ifs with hex
  · obtain ⟨l, hl, hleq⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ.filter
      (fun l => l ≠ k ∧ b l i ≤ b k i)) ⟨hex.choose, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun hk => by have := hex.choose_spec; rw [hk] at this; exact lt_irrefl _ this,
          le_of_lt hex.choose_spec⟩⟩ (fun k => b k i)
    rw [hleq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    exact lt_of_lt_of_le (lt_of_le_of_ne hl.2 (hnt l k hl.1)) hk2
  · exact lt_of_lt_of_le (hpos k) hk2

/-- Per-item optimality of the greedy choice. -/
lemma item_opt {m n : ℕ} (b : Fin m → Fin n → ℝ) (i : Fin n) (δ : ℝ)
    (hpos : ∀ l, 0 < b l i) (hnt : ∀ a c, a ≠ c → b a i ≠ b c i)
    (hδ : top2 (fun l => b l i) ≠ δ) (y : Fin m → ℝ) (hy0 : ∀ k, 0 ≤ y k)
    (hy1 : ∑ k, y k ≤ 1) :
    0 ≤ ∑ k, (pay b i k - δ) *
        ((if Top (fun l => b l i) k ∧ δ ≤ top2 (fun l => b l i) then 1 else 0) - y k) ∧
      (∑ k, (pay b i k - δ) *
        ((if Top (fun l => b l i) k ∧ δ ≤ top2 (fun l => b l i) then 1 else 0) - y k) = 0 →
        ∀ k, y k = if Top (fun l => b l i) k ∧ δ ≤ top2 (fun l => b l i) then 1 else 0) := by
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · exact ⟨by simp, fun _ k => isEmptyElim k⟩
  obtain ⟨t, -, htmax⟩ := Finset.exists_max_image Finset.univ (fun l => b l i)
    Finset.univ_nonempty
  have ht : Top (fun l => b l i) t := fun l hl =>
    lt_of_le_of_ne (htmax l (Finset.mem_univ _)) (hnt l t hl)
  have huniq : ∀ k, Top (fun l => b l i) k → k = t := fun k hk => by
    by_contra h; exact lt_asymm (hk t (Ne.symm h)) (ht k h)
  set T := top2 (fun l => b l i) with hT
  have hpt : pay b i t = T := pay_top_eq b i t ht
  have hpk : ∀ k, k ≠ t → pay b i k < T := fun k hk => pay_lt_top2 b i t k ht hk hpos hnt
  have hsplit : ∀ f : Fin m → ℝ, ∑ k, f k = f t + ∑ k ∈ Finset.univ.erase t, f k := fun f =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ t)).symm
  have hg : ∀ k, k ≠ t →
      (if Top (fun l => b l i) k ∧ δ ≤ T then (1:ℝ) else 0) = 0 :=
    fun k hk => if_neg fun h => hk (huniq k h.1)
  rcases lt_or_gt_of_ne hδ with hlt | hgt
  · -- reserve not met: greedy allocates nothing
    have hg0 : ∀ k, (if Top (fun l => b l i) k ∧ δ ≤ T then (1:ℝ) else 0) = 0 :=
      fun k => if_neg fun h => absurd h.2 (not_le.mpr hlt)
    simp only [hg0]
    have hneg : ∀ k, pay b i k - δ < 0 := fun k => by
      by_cases hk : k = t
      · rw [hk, hpt]; linarith
      · linarith [hpk k hk]
    have hterm : ∀ k, 0 ≤ (pay b i k - δ) * (0 - y k) := fun k => by
      nlinarith [hneg k, hy0 k]
    refine ⟨Finset.sum_nonneg fun k _ => hterm k, fun h k => ?_⟩
    have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hterm k).mp h k (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (ne_of_lt (hneg k))
    · linarith
  · -- reserve met: greedy gives the item to `t`
    have hgt' : (if Top (fun l => b l i) t ∧ δ ≤ T then (1:ℝ) else 0) = 1 :=
      if_pos ⟨ht, le_of_lt hgt⟩
    rw [hsplit, hgt', hpt]
    have hrest : ∑ k ∈ Finset.univ.erase t, (pay b i k - δ) *
        ((if Top (fun l => b l i) k ∧ δ ≤ T then (1:ℝ) else 0) - y k) =
        ∑ k ∈ Finset.univ.erase t, -((pay b i k - δ) * y k) :=
      Finset.sum_congr rfl fun k hk => by rw [hg k (Finset.ne_of_mem_erase hk)]; ring
    rw [hrest]
    set s := ∑ k ∈ Finset.univ.erase t, y k with hs
    have hy1' : y t + s ≤ 1 := by rw [hsplit] at hy1; exact hy1
    have hiden : (T - δ) * (1 - y t) + ∑ k ∈ Finset.univ.erase t, -((pay b i k - δ) * y k) =
        (T - δ) * (1 - y t - s) + ∑ k ∈ Finset.univ.erase t, (T - pay b i k) * y k := by
      have e1 : ∑ k ∈ Finset.univ.erase t, (T - pay b i k) * y k =
          (T - δ) * s + ∑ k ∈ Finset.univ.erase t, -((pay b i k - δ) * y k) := by
        rw [hs, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e1]; ring
    rw [hiden]
    have hA : 0 ≤ (T - δ) * (1 - y t - s) := mul_nonneg (by linarith) (by linarith)
    have hterm : ∀ k ∈ Finset.univ.erase t, 0 ≤ (T - pay b i k) * y k := fun k hk =>
      mul_nonneg (by linarith [hpk k (Finset.ne_of_mem_erase hk)]) (hy0 k)
    have hB := Finset.sum_nonneg hterm
    refine ⟨by linarith, fun h k => ?_⟩
    have hA0 : (T - δ) * (1 - y t - s) = 0 := by linarith
    have hB0 : ∑ k ∈ Finset.univ.erase t, (T - pay b i k) * y k = 0 := by linarith
    have hyk : ∀ k ∈ Finset.univ.erase t, y k = 0 := fun k hk => by
      have := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hB0 k hk
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd h1 (ne_of_gt (by linarith [hpk k (Finset.ne_of_mem_erase hk)]))
      · exact h1
    by_cases hk : k = t
    · subst hk
      rw [hgt']
      have hs0 : s = 0 := by rw [hs]; exact Finset.sum_eq_zero hyk
      rcases mul_eq_zero.mp hA0 with h1 | h1
      · linarith
      · linarith
    · rw [hg k hk]; exact hyk k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩)

lemma objective_eq (M : Market) (b : Fin M.m → Fin M.n → ℝ) (Y : Fin M.n → Fin M.m → ℝ) :
    objective M b Y = ∑ i, (M.δ + ∑ k, (pay b i k - M.δ) * Y i k) := by
  unfold objective
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_sub, mul_one, Finset.mul_sum]
  have : ∑ k, (pay b i k - M.δ) * Y i k = ∑ k, (pay b i k * Y i k - M.δ * Y i k) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [this, Finset.sum_sub_distrib]; ring

end EndogLemma6Aux

open EndogBudgetAds.Equilibrium EndogLemma6Aux in
theorem solution (M : Market) (hM : M.Standing) (j : Fin M.m) (V : Valuations M)
    (hVpos : ∀ l i, 0 < V l i) (hW : NoTies (W M V))
    (hδ : ∀ i, top2 (fun l => W M V l i) ≠ M.δ)
    (hV : V ∈ EventJ M j (sigmaStar M j)) :
    ∀ Y, AllocOptimal M (budgetsOf (sigmaStar M) V) (bidsOf (sigmaStar M) V) Y →
      IsGreedy M (bidsOf (sigmaStar M) V) Y := by
  intro Y hY
  set b := bidsOf (sigmaStar M) V with hbdef
  have hbW : ∀ l i, b l i = W M V l i := fun l i => rfl
  have hpos : ∀ i l, 0 < b l i := fun i l => by
    rw [hbW]; unfold W
    have := hM.r_nonneg l
    have := hVpos l i
    positivity
  have hnt : ∀ i a c, a ≠ c → b a i ≠ b c i := fun i a c hac => by
    rw [hbW, hbW]; exact hW i a c hac
  have hδ' : ∀ i, top2 (fun l => b l i) ≠ M.δ := hδ
  -- the greedy allocation
  set g : Fin M.n → Fin M.m → ℝ := fun i k =>
    if Top (fun l => b l i) k ∧ M.δ ≤ top2 (fun l => b l i) then 1 else 0 with hgdef
  -- budgets have slack: `Ψ̄_k < B*_k` for every `k`
  have hdev : deviate (sigmaStar M) j (sigmaStar M j) = sigmaStar M := by
    unfold deviate; exact Function.update_eq_self _ _
  have hslack : ∀ k, PsiBar M k V < budgetsOf (sigmaStar M) V k := by
    intro k
    show PsiBar M k V < Bstar M k (V k)
    obtain ⟨hk, hj⟩ := hV
    by_cases hkj : k = j
    · rw [hkj]; exact hj
    · have h1 := hk k hkj
      have hXi : 0 ≤ Xi M j k (sigmaStar M j) V := by
        unfold Xi
        rw [hdev]
        have e1 : ∀ i, 0 ≤ (if EndogBudgetAds.Equilibrium.IsTop (fun l => W M V l i) k ∧
            IsSecond (fun l => bidsOf (sigmaStar M) V l i) j then
            bidsOf (sigmaStar M) V j i - top2 (fun l => W M V l i) else 0) := fun i => by
          split_ifs with h
          · have := top2_le_second (x := fun l => W M V l i) h.1 h.2
            change top2 (fun l => W M V l i) ≤ W M V j i at this
            change 0 ≤ W M V j i - top2 (fun l => W M V l i)
            linarith
          · exact le_rfl
        have e2 : ∀ i, (if EndogBudgetAds.Equilibrium.IsTop (fun l => W M V l i) k ∧
            EndogBudgetAds.Equilibrium.IsTop (fun l => bidsOf (sigmaStar M) V l i) j then
            top2Excl (fun l => W M V l i) j else 0) = 0 := fun i =>
          if_neg fun h => lt_asymm (h.1 j (Ne.symm hkj)) (h.2 k hkj)
        have e3 : ∀ i, 0 ≤ (if EndogBudgetAds.Equilibrium.IsTop (fun l => W M V l i) j ∧
            IsSecond (fun l => W M V l i) k then top2 (fun l => W M V l i) else 0) := fun i => by
          split_ifs
          · exact top2_nonneg_pos _ (fun l => hpos i l)
          · exact le_rfl
        simp only [e2, Finset.sum_const_zero, sub_zero]
        exact add_nonneg (Finset.sum_nonneg fun i _ => e1 i) (Finset.sum_nonneg fun i _ => e3 i)
      linarith
  -- feasibility of the greedy allocation
  have hgfeas : AllocFeasible M (budgetsOf (sigmaStar M) V) b g := by
    refine ⟨fun i k => by simp only [hgdef]; split_ifs <;> norm_num, fun k => ?_, fun i => ?_⟩
    · refine le_trans ?_ (le_of_lt (hslack k))
      show _ ≤ ∑ i, if Top (fun l => b l i) k then top2 (fun l => b l i) else 0
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [hgdef]
      by_cases h : Top (fun l => b l i) k ∧ M.δ ≤ top2 (fun l => b l i)
      · rw [if_pos h, mul_one, pay_top_eq b i k h.1, if_pos h.1]
      · rw [if_neg h, mul_zero]
        split_ifs
        · exact top2_nonneg_pos _ (fun l => hpos i l)
        · exact le_rfl
    · simp only [hgdef]
      by_cases hex : ∃ t, Top (fun l => b l i) t
      · obtain ⟨t, ht⟩ := hex
        rw [Finset.sum_eq_single t]
        · split_ifs <;> norm_num
        · intro k _ hkt
          exact if_neg fun h => lt_asymm (h.1 t (Ne.symm hkt)) (ht k hkt)
        · intro h; exact absurd (Finset.mem_univ t) h
      · push_neg at hex
        rw [Finset.sum_eq_zero fun k _ => if_neg fun h => hex k h.1]
        norm_num
  -- compare objectives
  have hle := hY.2 g hgfeas
  rw [objective_eq, objective_eq] at hle
  have hfY := hY.1
  have hitem := fun i => item_opt b i M.δ (hpos i) (hnt i) (hδ' i) (fun k => Y i k)
    (fun k => hfY.1 i k) (hfY.2.2 i)
  have hdiff : ∑ i, (M.δ + ∑ k, (pay b i k - M.δ) * g i k) -
      ∑ i, (M.δ + ∑ k, (pay b i k - M.δ) * Y i k) =
      ∑ i, ∑ k, (pay b i k - M.δ) * (g i k - Y i k) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hsum0 : ∑ i, ∑ k, (pay b i k - M.δ) * (g i k - Y i k) = 0 := by
    have h1 : 0 ≤ ∑ i, ∑ k, (pay b i k - M.δ) * (g i k - Y i k) :=
      Finset.sum_nonneg fun i _ => (hitem i).1
    linarith
  intro i k
  have hi0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => (hitem i).1).mp hsum0 i
    (Finset.mem_univ _)
  exact (hitem i).2 hi0 k

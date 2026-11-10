-- Prove2me | solution 1 for BudgetFeasibleClockAuctions.SymmetricPostedPrice.mechanism5_logarithmic_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T06:56:15.225243+00:00
-- url     : https://prove2.me/submissions/bc37b6eb-4c58-4714-9ef8-42a78759fa3e

import Mathlib
import Definitions.Def_BudgetClock_PostedSym_Setting

set_option autoImplicit false

open BudgetClock.PostedSym

namespace BudgetClock.PostedSym.M5Aux

lemma offerPrice_succ_le (n : ℕ) {B : ℝ} (hB : 0 ≤ B) (a : ℕ) :
    offerPrice n B (a + 1) ≤ offerPrice n B a := by
  have hL := Real.log_natCast_nonneg n
  rcases hL.lt_or_eq with hL | hL
  · unfold offerPrice
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
      rw [if_neg (by omega), if_neg (by omega)]
      apply div_le_div_of_nonneg_left hB
      · exact mul_pos (mul_pos (by linarith) two_pos) hL
      · push_cast; nlinarith
  · unfold offerPrice; rw [← hL]; simp

/-- Invariant of the scan of Mechanism 5 after processing the bidders of `P`. -/
structure Inv (n : ℕ) (B : ℝ) (c : Fin n → ℝ) (P : Finset (Fin n)) (s : ScanState n) : Prop where
  card : s.count = s.winners.card
  sub : s.winners ⊆ P
  rej : ∀ i ∈ P, i ∉ s.winners → offerPrice n B s.count < c i
  pay : ∑ i ∈ s.winners, s.price i = ∑ k ∈ Finset.range s.count, offerPrice n B k

lemma inv_step {n : ℕ} {B : ℝ} {c : Fin n → ℝ} (hB : 0 ≤ B) (P : Finset (Fin n))
    (s : ScanState n) (i : Fin n) (hi : i ∉ P) (h : Inv n B c P s) :
    Inv n B c (insert i P) (step n B c s i) := by
  have hiW : i ∉ s.winners := fun h' => hi (h.sub h')
  unfold step
  split_ifs with hc
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp only
      rw [Finset.card_insert_of_notMem hiW, h.card]
    · exact Finset.insert_subset_insert i h.sub
    · intro i' hi' hnot
      simp only [Finset.mem_insert, not_or] at hnot hi'
      rcases hi' with h1 | hi'
      · exact absurd h1 hnot.1
      · exact lt_of_le_of_lt (offerPrice_succ_le n hB _) (h.rej i' hi' hnot.2)
    · simp only
      have hupd : ∑ x ∈ s.winners, Function.update s.price i (offerPrice n B s.count) x =
          ∑ x ∈ s.winners, s.price x :=
        Finset.sum_congr rfl (fun x hx => Function.update_of_ne (by rintro rfl; exact hiW hx) _ _)
      rw [Finset.sum_insert hiW, Finset.sum_range_succ, Function.update_self, hupd, h.pay]
      ring
  · refine ⟨h.card, h.sub.trans (Finset.subset_insert _ _), ?_, ?_⟩
    · intro i' hi' hnot
      rcases Finset.mem_insert.1 hi' with h1 | hi'
      · subst h1; exact lt_of_not_ge hc
      · exact h.rej i' hi' hnot
    · simp only
      have hupd : ∑ x ∈ s.winners, Function.update s.price i (offerPrice n B s.count) x =
          ∑ x ∈ s.winners, s.price x :=
        Finset.sum_congr rfl (fun x hx => Function.update_of_ne (by rintro rfl; exact hiW hx) _ _)
      rw [hupd, h.pay]

lemma inv_foldl {n : ℕ} {B : ℝ} {c : Fin n → ℝ} (hB : 0 ≤ B) :
    ∀ (l : List (Fin n)) (P : Finset (Fin n)) (s : ScanState n),
    l.Nodup → (∀ x ∈ l, x ∉ P) → Inv n B c P s →
      Inv n B c (P ∪ l.toFinset) (l.foldl (step n B c) s)
  | [], P, s, _, _, h => by simpa using h
  | x :: l, P, s, hnd, hdisj, h => by
    rw [List.foldl_cons]
    have hnd' := List.nodup_cons.1 hnd
    have hx : x ∉ P := hdisj x (by simp)
    have := inv_foldl hB l (insert x P) (step n B c s x) hnd'.2 (by
      intro y hy hyP
      rcases Finset.mem_insert.1 hyP with h1 | hyP
      · subst h1; exact hnd'.1 hy
      · exact hdisj y (List.mem_cons_of_mem _ hy) hyP) (inv_step hB P s x hx h)
    have hset : P ∪ (x :: l).toFinset = insert x P ∪ l.toFinset := by
      ext y
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      tauto
    rw [hset]
    exact this

lemma inv_scan {n : ℕ} {B : ℝ} {c : Fin n → ℝ} (hB : 0 ≤ B) (j : Fin n) :
    Inv n B c (Finset.univ.erase j) (scan n B c j) := by
  have h0 : Inv n B c ∅ ({ count := 0, winners := ∅, price := fun _ => 0 } : ScanState n) :=
    ⟨by simp, by simp, by simp, by simp⟩
  have := inv_foldl (c := c) hB ((List.finRange n).filter (fun i => i ≠ j)) ∅ _
    (List.Nodup.filter _ (List.nodup_finRange n)) (by simp) h0
  have hset : Finset.univ.erase j = ∅ ∪ ((List.finRange n).filter (fun i => i ≠ j)).toFinset := by
    ext y; simp
  unfold scan
  rw [hset]
  exact this

/-- Weights: `offerPrice n B k = B / (2 ln n) * w k`. -/
noncomputable def w (k : ℕ) : ℝ := if k = 0 then 1 else 1 / (k : ℝ)

lemma w_nonneg (k : ℕ) : 0 ≤ w k := by
  unfold w; split_ifs <;> positivity

lemma W_le (m : ℕ) : ∑ k ∈ Finset.range (m + 1), w k ≤ 2 * Real.log ((m : ℝ) + 2) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have := Real.log_two_gt_d9
    norm_num [w]
    linarith
  · induction m, hm using Nat.le_induction with
    | base =>
      have h3 : 1 < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have := Real.exp_one_lt_d9
        linarith
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num [w]
      linarith
    | succ m hm ih =>
      rw [Finset.sum_range_succ]
      have hw : w (m + 1) = 1 / ((m : ℝ) + 1) := by simp [w]
      rw [hw]
      have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
      have hx : 0 < ((m : ℝ) + 2) / ((m : ℝ) + 3) := by positivity
      have hlog := Real.log_le_sub_one_of_pos hx
      rw [Real.log_div (by positivity) (by positivity)] at hlog
      set t : ℝ := 1 / ((m : ℝ) + 3) with ht
      have h1 : ((m : ℝ) + 2) / ((m : ℝ) + 3) - 1 = -t := by
        rw [ht]; field_simp; ring
      rw [h1] at hlog
      have h2 : 1 / ((m : ℝ) + 1) ≤ 2 * t := by
        rw [ht, div_le_iff₀ (by positivity)]
        rw [show 2 * (1 / ((m : ℝ) + 3)) * ((m : ℝ) + 1) = (2 * (m : ℝ) + 2) / ((m : ℝ) + 3) by
          field_simp]
        rw [le_div_iff₀ (by positivity)]
        linarith
      have h4 : ((↑(m + 1) : ℝ) + 2) = (m : ℝ) + 3 := by push_cast; ring
      rw [h4]
      linarith

lemma offerPrice_eq (n : ℕ) (hn : 2 ≤ n) (B : ℝ) (k : ℕ) :
    offerPrice n B k = B / (2 * Real.log n) * w k := by
  have h1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hL : 0 < Real.log n := Real.log_pos h1
  unfold offerPrice w
  split_ifs with hk
  · ring
  · have : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    field_simp

lemma sum_offer_le (n : ℕ) (hn : 2 ≤ n) {B : ℝ} (hB : 0 ≤ B) (a : ℕ) (ha : a + 1 ≤ n) :
    ∑ k ∈ Finset.range a, offerPrice n B k ≤ B := by
  have h1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hL : 0 < Real.log n := Real.log_pos h1
  simp_rw [offerPrice_eq n hn B]
  rw [← Finset.mul_sum]
  have hs : ∑ k ∈ Finset.range a, w k ≤ ∑ k ∈ Finset.range (n - 2 + 1), w k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      (fun k _ _ => w_nonneg k)
  have h2 := W_le (n - 2)
  have h3 : ((n - 2 : ℕ) : ℝ) + 2 = n := by
    rw [Nat.cast_sub hn]; push_cast; ring
  rw [h3] at h2
  calc B / (2 * Real.log n) * ∑ k ∈ Finset.range a, w k
      ≤ B / (2 * Real.log n) * (2 * Real.log n) :=
        mul_le_mul_of_nonneg_left (hs.trans h2) (div_nonneg hB (by linarith))
    _ = B := by field_simp

lemma avg (n : ℕ) (r : ℕ → ℝ) (hmono : ∀ k l, k ≤ l → l < n → r l ≤ r k)
    (a : ℕ) (_ha : 1 ≤ a) : ∀ m, a ≤ m → m ≤ n →
      (a : ℝ) * ∑ k ∈ Finset.range m, r k ≤ m * ∑ k ∈ Finset.range a, r k := by
  intro m ham
  induction m, ham using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ m hm ih =>
    intro hmn
    have ih := ih (by omega)
    rw [Finset.sum_range_succ]
    have hrm : (a : ℝ) * r m ≤ ∑ k ∈ Finset.range a, r k := by
      have := Finset.card_nsmul_le_sum (Finset.range a) r (r m)
        (fun k hk => hmono k m (by simp at hk; omega) (by omega))
      simpa using this
    push_cast
    nlinarith

lemma mech5_facts (n : ℕ) (B : ℝ) (c : Fin n → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hcB : ∀ i, c i ≤ B) (j : Fin n) :
    (∑ i ∈ (mech5 n B c j).1, (mech5 n B c j).2 i) ≤ B ∧
      ∃ a : ℕ, 1 ≤ a ∧ (mech5 n B c j).1.card = a ∧
        ∀ i, i ≠ j → i ∉ (mech5 n B c j).1 → B / ((a : ℝ) * 2 * Real.log n) < c i := by
  have hB : 0 ≤ B := (hc0 j).trans (hcB j)
  have hI := inv_scan (c := c) hB j
  have hcard_le : (scan n B c j).count + 1 ≤ n := by
    rw [hI.card]
    have := Finset.card_le_card hI.sub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
    have : 0 < n := Fin.pos j
    omega
  simp only [mech5]
  generalize scan n B c j = s at hI hcard_le ⊢
  by_cases h0 : s.count = 0
  · rw [if_pos h0, if_pos (hcB j)]
    have hW0 : s.winners = ∅ := by rw [← Finset.card_eq_zero, ← hI.card, h0]
    rw [hW0]
    refine ⟨by simp, 1, le_refl _, by simp, ?_⟩
    intro i hij hiW
    have := hI.rej i (by simp [hij]) (by rw [hW0]; simp)
    rw [h0] at this
    simpa [offerPrice] using this
  · rw [if_neg h0]
    refine ⟨?_, s.count, Nat.pos_of_ne_zero h0, hI.card.symm, ?_⟩
    · rw [hI.pay]
      exact sum_offer_le n (by omega) hB _ hcard_le
    · intro i hij hiW
      have := hI.rej i (by simp [hij]) hiW
      simpa [offerPrice, h0] using this

theorem main (n : ℕ) (v : Finset (Fin n) → ℝ)
    (hv : IsSymmetricSubmodular n v) (B : ℝ) (c : Fin n → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hcB : ∀ i, c i ≤ B) (j : Fin n) :
    (∑ i ∈ (mech5 n B c j).1, (mech5 n B c j).2 i) ≤ B ∧
    ∀ O : Finset (Fin n), (∑ i ∈ O, c i) ≤ B →
      v O ≤ (2 + 2 * Real.log n) * v (mech5 n B c j).1 ∧
      (2 ≤ n → v O ≤ (5 * Real.log n) * v (mech5 n B c j).1) := by
  have hB : 0 ≤ B := (hc0 j).trans (hcB j)
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  obtain ⟨hpay, a, ha1, hWcard, hrej⟩ := mech5_facts n B c hc0 hcB j
  refine ⟨hpay, ?_⟩
  intro O hO
  obtain ⟨r, hr0, hmono, hvS⟩ := hv
  set W := (mech5 n B c j).1 with hWdef
  have han : a ≤ n := by
    rw [← hWcard]; simpa using Finset.card_le_univ W
  have ha1' : (1:ℝ) ≤ a := by exact_mod_cast ha1
  -- bidders of O outside W and other than j
  set R := (O \ W).erase j with hR
  have hRcard : (R.card : ℝ) ≤ (a : ℝ) * 2 * Real.log n := by
    rcases R.eq_empty_or_nonempty with hRe | ⟨i, hi⟩
    · rw [hRe]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
    · have hij : i ≠ j := (Finset.mem_erase.1 hi).1
      have hiO : i ∈ O \ W := (Finset.mem_erase.1 hi).2
      have hn2 : 2 ≤ n := by
        have h1 := i.isLt; have h2 := j.isLt
        have : i.val ≠ j.val := fun h => hij (Fin.ext h)
        omega
      have h1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      have hLp : 0 < Real.log n := Real.log_pos h1
      have hden : 0 < (a : ℝ) * 2 * Real.log n := by positivity
      have hq0 : 0 ≤ B / ((a : ℝ) * 2 * Real.log n) := div_nonneg hB hden.le
      have hlt := hrej i hij (Finset.mem_sdiff.1 hiO).2
      have hBpos : 0 < B := lt_of_le_of_lt hq0 (lt_of_lt_of_le hlt (hcB i))
      have hsum : R.card • (B / ((a : ℝ) * 2 * Real.log n)) ≤ ∑ x ∈ R, c x :=
        Finset.card_nsmul_le_sum R c _ (fun x hx => le_of_lt (hrej x (Finset.mem_erase.1 hx).1
          (Finset.mem_sdiff.1 (Finset.mem_erase.1 hx).2).2))
      have hRO : ∑ x ∈ R, c x ≤ ∑ x ∈ O, c x :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => (Finset.mem_sdiff.1 (Finset.mem_erase.1 hx).2).1) (fun x _ _ => hc0 x)
      rw [nsmul_eq_mul] at hsum
      have hq : (R.card : ℝ) * (B / ((a : ℝ) * 2 * Real.log n)) ≤ B := by linarith
      rw [mul_div_assoc', div_le_iff₀ hden] at hq
      have hq' : (R.card : ℝ) * B ≤ ((a : ℝ) * 2 * Real.log n) * B := by linarith
      exact le_of_mul_le_mul_right hq' hBpos
  have hOcard : (O.card : ℝ) ≤ (a : ℝ) * (2 + 2 * Real.log n) := by
    have hsub : O ⊆ insert j (W ∪ R) := by
      intro x hx
      by_cases hxj : x = j
      · exact Finset.mem_insert.2 (Or.inl hxj)
      · by_cases hxW : x ∈ W
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hxW)
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
            (Finset.mem_erase.2 ⟨hxj, Finset.mem_sdiff.2 ⟨hx, hxW⟩⟩))
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le j (W ∪ R)
    have h3 := Finset.card_union_le W R
    have h4 : (O.card : ℝ) ≤ (a : ℝ) + 1 + R.card := by
      rw [← hWcard]; exact_mod_cast (by omega : O.card ≤ W.card + 1 + R.card)
    nlinarith
  have hvW : v W = ∑ k ∈ Finset.range a, r k := by rw [hvS, hWcard]
  have hvO : v O = ∑ k ∈ Finset.range O.card, r k := hvS O
  have hvW0 : 0 ≤ v W := by
    rw [hvW]; exact Finset.sum_nonneg (fun k hk => hr0 k (by simp at hk; omega))
  have hmain : v O ≤ (2 + 2 * Real.log n) * v W := by
    rcases le_total O.card a with hle | hle
    · have : v O ≤ v W := by
        rw [hvO, hvW]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hle)
          (fun k hk _ => hr0 k (by simp at hk; omega))
      nlinarith
    · have hOn : O.card ≤ n := by simpa using Finset.card_le_univ O
      have h := avg n r hmono a ha1 O.card hle hOn
      rw [← hvO, ← hvW] at h
      have h' : (a : ℝ) * v O ≤ (a : ℝ) * ((2 + 2 * Real.log n) * v W) := by nlinarith
      exact le_of_mul_le_mul_left h' (by linarith)
  refine ⟨hmain, fun hn2 => ?_⟩
  have hlog2 := Real.log_two_gt_d9
  have hmon : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hfac : 2 + 2 * Real.log n ≤ 5 * Real.log n := by norm_num at hlog2; linarith
  exact hmain.trans (mul_le_mul_of_nonneg_right hfac hvW0)

end BudgetClock.PostedSym.M5Aux

open BudgetClock.PostedSym in
theorem solution (n : ℕ) (v : Finset (Fin n) → ℝ)
    (hv : IsSymmetricSubmodular n v) (B : ℝ) (c : Fin n → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hcB : ∀ i, c i ≤ B) (j : Fin n) :
    (∑ i ∈ (mech5 n B c j).1, (mech5 n B c j).2 i) ≤ B ∧
    ∀ O : Finset (Fin n), (∑ i ∈ O, c i) ≤ B →
      v O ≤ (2 + 2 * Real.log n) * v (mech5 n B c j).1 ∧
      (2 ≤ n → v O ≤ (5 * Real.log n) * v (mech5 n B c j).1) := by
  exact BudgetClock.PostedSym.M5Aux.main n v hv B c hc0 hcB j

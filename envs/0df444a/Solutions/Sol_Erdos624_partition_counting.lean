-- Prove2me | solution 1 for Erdos624.partition_counting
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T05:30:43.02843+00:00
-- url     : https://prove2.me/submissions/afe1a7aa-3d28-4c77-8fb8-5acba68d8afc

import Mathlib
namespace E624R7
open Finset Nat Function

lemma choose_transfer (t a b : ℕ) (h : b + 2 ≤ a) :
    (a - 1).choose t + (b + 1).choose t ≤ a.choose t + b.choose t := by
  have ha : 0 < a := by lia
  cases t with
  | zero => simp
  | succ t =>
    have hba : b ≤ a - 1 := by lia
    have ha_eq : a = Nat.succ (a - 1) := (Nat.sub_add_cancel ha).symm
    rw [ha_eq]
    change (a - 1).choose t.succ + (b + 1).choose t.succ ≤
      (a - 1).succ.choose t.succ + b.choose t.succ
    rw [choose_succ_succ]
    change (a - 1).choose t.succ + b.succ.choose t.succ ≤
      (a - 1).choose t + (a - 1).choose t.succ + b.choose t.succ
    rw [choose_succ_succ]
    have : b.choose t ≤ (a - 1).choose t := choose_le_choose t hba
    lia

def sumSq {q : ℕ} (c : Fin q → ℕ) : ℕ := ∑ i : Fin q, c i * c i

lemma sumSq_transfer_lt {q : ℕ} (c : Fin q → ℕ) (i j : Fin q) (hij : i ≠ j)
    (h : c j + 2 ≤ c i) :
    sumSq (update (update c i (c i - 1)) j (c j + 1)) < sumSq c := by
  classical
  unfold sumSq
  set c' := update (update c i (c i - 1)) j (c j + 1) with hc'
  have hi : c' i = c i - 1 := by rw [hc', update_of_ne hij, update_self]
  have hj : c' j = c j + 1 := by rw [hc', update_self]
  have hrest : ∀ k, k ≠ i → k ≠ j → c' k = c k := by
    intro k hki hkj; rw [hc', update_of_ne hkj, update_of_ne hki]
  have Hx : ∑ k, c' k * c' k =
      (∑ k ∈ (univ.erase i).erase j, c' k * c' k) + c' i * c' i + c' j * c' j := by
    have e1 := (sum_erase_add (s := univ) (f := fun k => c' k * c' k) (mem_univ i)).symm
    have hjmem : j ∈ univ.erase i := by simp [Ne.symm hij]
    have e2 := (sum_erase_add (s := univ.erase i) (f := fun k => c' k * c' k) hjmem).symm
    calc ∑ k, c' k * c' k
        = ∑ k ∈ univ.erase i, c' k * c' k + c' i * c' i := e1
      _ = (∑ k ∈ (univ.erase i).erase j, c' k * c' k + c' j * c' j) + c' i * c' i := by rw [e2]
      _ = _ := by ring
  have Hy : ∑ k, c k * c k =
      (∑ k ∈ (univ.erase i).erase j, c k * c k) + c i * c i + c j * c j := by
    have e1 := (sum_erase_add (s := univ) (f := fun k => c k * c k) (mem_univ i)).symm
    have hjmem : j ∈ univ.erase i := by simp [Ne.symm hij]
    have e2 := (sum_erase_add (s := univ.erase i) (f := fun k => c k * c k) hjmem).symm
    calc ∑ k, c k * c k
        = ∑ k ∈ univ.erase i, c k * c k + c i * c i := e1
      _ = (∑ k ∈ (univ.erase i).erase j, c k * c k + c j * c j) + c i * c i := by rw [e2]
      _ = _ := by ring
  have Hrest : ∑ k ∈ (univ.erase i).erase j, c' k * c' k =
      ∑ k ∈ (univ.erase i).erase j, c k * c k := by
    apply sum_congr rfl; intro k hk
    have hk' : k ≠ j ∧ k ≠ i := by simpa [mem_erase] using hk
    rw [hrest k hk'.2 hk'.1]
  rw [Hx, Hy, Hrest, hi, hj]
  have ha : 1 ≤ c i := by lia
  have : (c i - 1) * (c i - 1) + (c j + 1) * (c j + 1) < c i * c i + c j * c j := by
    nlinarith [Nat.sub_add_cancel ha]
  lia

lemma sum_choose_transfer_le {q : ℕ} (c : Fin q → ℕ) (t : ℕ) (i j : Fin q)
    (hij : i ≠ j) (h : c j + 2 ≤ c i) :
    ∑ k, (update (update c i (c i - 1)) j (c j + 1) k).choose t ≤ ∑ k, (c k).choose t := by
  classical
  set c' := update (update c i (c i - 1)) j (c j + 1) with hc'
  have hi : c' i = c i - 1 := by rw [hc', update_of_ne hij, update_self]
  have hj : c' j = c j + 1 := by rw [hc', update_self]
  have hrest : ∀ k, k ≠ i → k ≠ j → c' k = c k := by
    intro k hki hkj; rw [hc', update_of_ne hkj, update_of_ne hki]
  have Hx : ∑ k, (c' k).choose t =
      (∑ k ∈ (univ.erase i).erase j, (c' k).choose t) + (c' i).choose t + (c' j).choose t := by
    have e1 := (sum_erase_add (s := univ) (f := fun k => (c' k).choose t) (mem_univ i)).symm
    have hjmem : j ∈ univ.erase i := by simp [Ne.symm hij]
    have e2 := (sum_erase_add (s := univ.erase i) (f := fun k => (c' k).choose t) hjmem).symm
    calc ∑ k, (c' k).choose t
        = ∑ k ∈ univ.erase i, (c' k).choose t + (c' i).choose t := e1
      _ = (∑ k ∈ (univ.erase i).erase j, (c' k).choose t + (c' j).choose t)
            + (c' i).choose t := by rw [e2]
      _ = _ := by ring
  have Hy : ∑ k, (c k).choose t =
      (∑ k ∈ (univ.erase i).erase j, (c k).choose t) + (c i).choose t + (c j).choose t := by
    have e1 := (sum_erase_add (s := univ) (f := fun k => (c k).choose t) (mem_univ i)).symm
    have hjmem : j ∈ univ.erase i := by simp [Ne.symm hij]
    have e2 := (sum_erase_add (s := univ.erase i) (f := fun k => (c k).choose t) hjmem).symm
    calc ∑ k, (c k).choose t
        = ∑ k ∈ univ.erase i, (c k).choose t + (c i).choose t := e1
      _ = (∑ k ∈ (univ.erase i).erase j, (c k).choose t + (c j).choose t)
            + (c i).choose t := by rw [e2]
      _ = _ := by ring
  have Hrest : ∑ k ∈ (univ.erase i).erase j, (c' k).choose t =
      ∑ k ∈ (univ.erase i).erase j, (c k).choose t := by
    apply sum_congr rfl; intro k hk
    have hk' : k ≠ j ∧ k ≠ i := by simpa [mem_erase] using hk
    rw [hrest k hk'.2 hk'.1]
  rw [Hx, Hy, Hrest, hi, hj]
  linarith [choose_transfer t (c i) (c j) h]

lemma sum_after_transfer {q : ℕ} (c : Fin q → ℕ) (i j : Fin q) (hij : i ≠ j)
    (h : 1 ≤ c i) :
    ∑ k, update (update c i (c i - 1)) j (c j + 1) k = ∑ k, c k := by
  classical
  -- Use sum_congr comparing pointwise, or unfold via erase
  set c1 := update c i (c i - 1)
  set c' := update c1 j (c j + 1)
  have hi1 : c1 i = c i - 1 := update_self _ _ _
  have hj1 : c1 j = c j := update_of_ne (Ne.symm hij) _ _
  have hj' : c' j = c j + 1 := update_self _ _ _
  have hi' : c' i = c i - 1 := by rw [show c' = update c1 j (c j + 1) from rfl, update_of_ne hij, hi1]
  have hrest : ∀ k, k ≠ i → k ≠ j → c' k = c k := by
    intro k hki hkj
    simp [c', c1, update_of_ne hkj, update_of_ne hki]
  have e1 := (sum_erase_add (s := univ) (f := c') (mem_univ i)).symm
  have hjmem : j ∈ univ.erase i := by simp [Ne.symm hij]
  have e2 := (sum_erase_add (s := univ.erase i) (f := c') hjmem).symm
  have f1 := (sum_erase_add (s := univ) (f := c) (mem_univ i)).symm
  have f2 := (sum_erase_add (s := univ.erase i) (f := c) hjmem).symm
  have Hrest : ∑ k ∈ (univ.erase i).erase j, c' k = ∑ k ∈ (univ.erase i).erase j, c k := by
    apply sum_congr rfl; intro k hk
    have hk' : k ≠ j ∧ k ≠ i := by simpa [mem_erase] using hk
    exact hrest k hk'.2 hk'.1
  calc ∑ k, c' k
      = ∑ k ∈ univ.erase i, c' k + c' i := e1
    _ = ∑ k ∈ (univ.erase i).erase j, c' k + c' j + c' i := by rw [e2]
    _ = ∑ k ∈ (univ.erase i).erase j, c k + (c j + 1) + (c i - 1) := by
        rw [Hrest, hj', hi']
    _ = ∑ k ∈ (univ.erase i).erase j, c k + c j + c i := by
        have := Nat.sub_add_cancel h; lia
    _ = ∑ k ∈ univ.erase i, c k + c i := by rw [← f2]
    _ = ∑ k, c k := by rw [← f1]






lemma sum_choose_ge_balanced {q : ℕ} [NeZero q] (c : Fin q → ℕ) (t N : ℕ)
    (hsum : ∑ i, c i = N) :
    q * (N / q).choose t ≤ ∑ i, (c i).choose t := by
  classical
  have key : ∀ μ, ∀ (c : Fin q → ℕ) (N : ℕ), sumSq c = μ → ∑ i, c i = N →
      q * (N / q).choose t ≤ ∑ i, (c i).choose t := by
    intro μ
    induction μ using Nat.strong_induction_on with
    | _ μ IH =>
      intro c N hμ hsum
      by_cases hbal : ∃ i j : Fin q, i ≠ j ∧ c j + 2 ≤ c i
      · obtain ⟨i, j, hij, hab⟩ := hbal
        set c' := update (update c i (c i - 1)) j (c j + 1)
        have hci : 1 ≤ c i := by lia
        have hsum' : ∑ k, c' k = N := by
          calc ∑ k, c' k = ∑ k, c k := by
                simpa [c'] using sum_after_transfer c i j hij hci
            _ = N := hsum
        have hμ' : sumSq c' < μ := by
          have := sumSq_transfer_lt c i j hij hab
          simpa [c', hμ] using this
        have := IH (sumSq c') hμ' c' N rfl hsum'
        have hch := sum_choose_transfer_le c t i j hij hab
        lia
      · have hclose : ∀ (i j : Fin q), c i ≤ c j + 1 := by
          intro i j
          by_cases hij : i = j
          · subst hij; exact Nat.le_succ_of_le le_rfl
          · by_contra hgt
            exact hbal ⟨i, j, hij, by lia⟩
        have hmin : ∀ i, N / q ≤ c i := by
          intro i
          by_contra hlt
          have hlt' : c i < N / q := Nat.not_le.mp hlt
          have hall : ∀ j, c j ≤ N / q := fun j =>
            (hclose j i).trans (Nat.succ_le_of_lt hlt')
          have hqpos : 0 < q := NeZero.pos q
          have hdivpos : 0 < N / q := lt_of_le_of_lt (Nat.zero_le _) hlt'
          have hi' : c i ≤ N / q - 1 := Nat.le_sub_one_of_lt hlt'
          have e := (sum_erase_add (s := (univ : Finset (Fin q))) (f := c) (mem_univ i)).symm
          have hcard_erase : #(univ.erase i) = q - 1 := by
            rw [Finset.card_erase_of_mem (mem_univ i), Finset.card_univ, Fintype.card_fin]
          have hsum_erase : ∑ j ∈ univ.erase i, (N / q) = (q - 1) * (N / q) := by
            rw [sum_const, hcard_erase]
            exact (nsmul_eq_mul _ _).trans (by rfl)
          have hdistrib : (q - 1) * (N / q) + (N / q) = q * (N / q) := by
            calc (q - 1) * (N / q) + (N / q)
                = (q - 1) * (N / q) + 1 * (N / q) := by rw [one_mul]
              _ = (q - 1 + 1) * (N / q) := (add_mul _ _ _).symm
              _ = q * (N / q) := by rw [Nat.sub_add_cancel hqpos]
          have hstrict : ∑ j, c j + 1 ≤ q * (N / q) := by
            have : ∑ j, c j ≤ (q - 1) * (N / q) + (N / q - 1) := by
              calc ∑ j, c j = ∑ j ∈ univ.erase i, c j + c i := e
                _ ≤ ∑ j ∈ univ.erase i, N / q + (N / q - 1) :=
                    _root_.add_le_add (sum_le_sum fun j _ => hall j) hi'
                _ = (q - 1) * (N / q) + (N / q - 1) := by rw [hsum_erase]
            have h2 : 1 ≤ N / q := hdivpos
            have : (q - 1) * (N / q) + (N / q - 1) + 1 = q * (N / q) := by
              rw [Nat.add_assoc, Nat.sub_add_cancel h2, hdistrib]
            lia
          have hle : q * (N / q) ≤ N := Nat.mul_div_le N q
          -- sum = N and sum + 1 ≤ q*(N/q) ≤ N ⇒ N+1 ≤ N
          lia
        have hsum_const : ∑ _i : Fin q, (N / q).choose t = q * (N / q).choose t := by
          rw [sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
        calc q * (N / q).choose t = ∑ _i : Fin q, (N / q).choose t := hsum_const.symm
          _ ≤ ∑ i, (c i).choose t :=
              sum_le_sum fun i _ => choose_le_choose t (hmin i)
  exact key (sumSq c) c N rfl hsum



lemma sum_range_succ_id (t : ℕ) :
    ∑ m ∈ range t, (m + 1) = t * (t + 1) / 2 := by
  -- Identify with ∑_{i ∈ range (t+1)} i via shift, then use Mathlib.
  have hshift : ∑ m ∈ range t, (m + 1) = ∑ m ∈ range (t + 1), m := by
    rw [sum_range_succ]
    -- ∑ range (t+1) = ∑ range t + t; need ∑(m+1) = ∑m + t
    have : ∑ m ∈ range t, (m + 1) = ∑ m ∈ range t, m + t := by
      simp [sum_add_distrib, sum_const, card_range]
    rw [this, add_comm]
  rw [hshift]
  -- ∑_{i=0}^{t} i = t(t+1)/2
  refine Nat.eq_div_of_mul_eq_right (by decide : (2 : ℕ) ≠ 0) ?_
  -- sum_range_id_mul_two (t+1) : (∑ range (t+1))*2 = (t+1)*t
  simpa [mul_comm] using sum_range_id_mul_two (t + 1)

lemma sum_qm (q t : ℕ) :
    ∑ m ∈ range t, q * (m + 1) = q * t * (t + 1) / 2 := by
  have hdiv : 2 ∣ t * (t + 1) := Even.two_dvd (Nat.even_mul_succ_self t)
  -- ∑ q*(m+1) = q * ∑(m+1) = q * (t(t+1)/2)
  rw [← mul_sum, sum_range_succ_id]
  -- q * (t*(t+1)/2) = q*t*(t+1)/2
  have hassoc : q * (t * (t + 1)) = q * t * (t + 1) := by ring
  calc q * (t * (t + 1) / 2)
      = q * (t * (t + 1)) / 2 := (Nat.mul_div_assoc q hdiv).symm
    _ = q * t * (t + 1) / 2 := by rw [hassoc]

/-- (N-a)(N-b) ≥ N(N-(a+b)) when a+b ≤ N. -/
lemma mul_sub_ge_mul_sub_add {N a b : ℕ} (hab : a + b ≤ N) :
    (N - a) * (N - b) ≥ N * (N - (a + b)) := by
  have ha : a ≤ N := le_trans (Nat.le_add_right a b) hab
  have hb : b ≤ N := le_trans (Nat.le_add_left b a) hab
  zify [ha, hb, hab]
  nlinarith

/-- Nat form of ∏(1-xᵢ) ≥ 1-∑xᵢ; requires nonempty s. -/
lemma prod_sub_ge_aux (N : ℕ) (s : Finset ℕ) (b : ℕ → ℕ)
    (hne : s.Nonempty) (hb : ∀ i ∈ s, b i ≤ N) (hsN : ∑ i ∈ s, b i ≤ N) :
    (∏ i ∈ s, (N - b i)) ≥ N ^ (s.card - 1) * (N - ∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hne).elim
  | insert x s hx ih =>
    rw [prod_insert hx, sum_insert hx, card_insert_of_notMem hx]
    by_cases hs : s = ∅
    · subst hs; simp
    · have hc : 1 ≤ s.card := card_pos.2 (nonempty_iff_ne_empty.2 hs)
      have hb' : ∀ i ∈ s, b i ≤ N := fun i hi => hb i (mem_insert_of_mem hi)
      have hsN'' : ∑ i ∈ s, b i ≤ N := by
        have htot := hsN; rw [sum_insert hx] at htot; lia
      have ih' := ih (nonempty_iff_ne_empty.2 hs) hb' hsN''
      have hmul := Nat.mul_le_mul_left (N - b x) ih'
      have hxN : b x ≤ N := hb x (mem_insert_self _ _)
      have htot : b x + ∑ i ∈ s, b i ≤ N := by rwa [← sum_insert hx]
      have key : (N - b x) * (N - ∑ i ∈ s, b i) ≥
          N * (N - (b x + ∑ i ∈ s, b i)) :=
        mul_sub_ge_mul_sub_add htot
      have hpow : N ^ (s.card + 1 - 1) = N * N ^ (s.card - 1) := by
        rw [Nat.add_sub_cancel]
        obtain ⟨n, hn⟩ : ∃ n, s.card = n + 1 := Nat.exists_eq_succ_of_ne_zero (by lia)
        rw [hn, Nat.add_sub_cancel, pow_succ, mul_comm]
      calc (N - b x) * ∏ i ∈ s, (N - b i)
          ≥ (N - b x) * (N ^ (s.card - 1) * (N - ∑ i ∈ s, b i)) := hmul
        _ = ((N - b x) * (N - ∑ i ∈ s, b i)) * N ^ (s.card - 1) := by ring
        _ ≥ (N * (N - (b x + ∑ i ∈ s, b i))) * N ^ (s.card - 1) :=
            Nat.mul_le_mul_right _ key
        _ = N ^ (s.card + 1 - 1) * (N - (b x + ∑ i ∈ s, b i)) := by
            rw [hpow]; ring

lemma choose_N_le_two_qpow_choose_s (q t N : ℕ) (hq : 0 < q) (ht : 0 < t)
    (hN : q * t * (t + 1) ≤ N) :
    N.choose t ≤ 2 * q ^ t * (N / q).choose t := by
  set s := N / q
  have hs_ge : t ≤ s := by
    have : t * (t + 1) ≤ N / q :=
      (Nat.le_div_iff_mul_le hq).2 (by convert hN using 1; ring)
    lia
  have hNge : t ≤ N := le_trans hs_ge (Nat.div_le_self N q)
  have hqm_le : ∀ m ∈ range t, q * (m + 1) ≤ N := by
    intro m hm
    have hm' : m + 1 ≤ t := Nat.succ_le_of_lt (mem_range.1 hm)
    calc q * (m + 1) ≤ q * t := Nat.mul_le_mul_left _ hm'
      _ ≤ q * t * (t + 1) := Nat.le_mul_of_pos_right _ (by lia)
      _ ≤ N := hN
  have hsum_qm := sum_qm q t
  have hsumle : ∑ m ∈ range t, q * (m + 1) ≤ N := by
    rw [hsum_qm]
    exact (Nat.div_le_self (q * t * (t + 1)) 2).trans hN
  have hne : (range t).Nonempty := by
    rw [Finset.nonempty_range_iff]; exact Nat.pos_iff_ne_zero.1 ht
  have hprod_ge : (∏ m ∈ range t, (N - q * (m + 1))) ≥
      N ^ (t - 1) * (N - ∑ m ∈ range t, q * (m + 1)) := by
    simpa [card_range] using
      prod_sub_ge_aux N (range t) (fun m => q * (m + 1)) hne hqm_le hsumle
  have he_qt : 2 ∣ q * t * (t + 1) := by
    have : 2 ∣ t * (t + 1) := Even.two_dvd (Nat.even_mul_succ_self t)
    have h := Dvd.dvd.mul_left this q
    -- q * (t * (t+1)) = q * t * (t+1)
    simpa [Nat.mul_assoc] using h
  have h2sum : 2 * ∑ m ∈ range t, q * (m + 1) ≤ N := by
    rw [hsum_qm]
    have : 2 * (q * t * (t + 1) / 2) = q * t * (t + 1) := by
      rw [Nat.mul_comm 2, Nat.div_mul_cancel he_qt]
    lia
  have h2 : N ≤ 2 * (N - ∑ m ∈ range t, q * (m + 1)) := by lia
  have hNt : N ^ t ≤ 2 * ∏ m ∈ range t, (N - q * (m + 1)) := by
    have hpow : N ^ t = N * N ^ (t - 1) := by
      obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 ht)
      rw [pow_succ, Nat.succ_sub_one, mul_comm]
    calc N ^ t = N * N ^ (t - 1) := hpow
      _ ≤ 2 * (N - ∑ m ∈ range t, q * (m + 1)) * N ^ (t - 1) :=
          Nat.mul_le_mul_right _ h2
      _ = 2 * (N ^ (t - 1) * (N - ∑ m ∈ range t, q * (m + 1))) := by ring
      _ ≤ 2 * ∏ m ∈ range t, (N - q * (m + 1)) := Nat.mul_le_mul_left _ hprod_ge
  have hleft : ∏ j ∈ range t, (N - j) ≤ N ^ t :=
    (prod_le_pow_card (range t) (fun j => N - j) N fun _ _ => Nat.sub_le _ _).trans_eq
      (by simp [card_range])
  have hqs : ∀ j ∈ range t, N - q * (j + 1) ≤ q * (s - j) := by
    intro j hj
    have hNbound : N ≤ q * (s + 1) := (Nat.lt_mul_div_succ N hq).le
    have hsj : j ≤ s := by have := mem_range.1 hj; lia
    have hsub : q * (s + 1) - q * (j + 1) = q * (s - j) := by
      rw [← Nat.mul_sub_left_distrib]; congr 1; lia
    calc N - q * (j + 1) ≤ q * (s + 1) - q * (j + 1) := Nat.sub_le_sub_right hNbound _
      _ = q * (s - j) := hsub
  have hright : ∏ m ∈ range t, (N - q * (m + 1)) ≤ q ^ t * ∏ j ∈ range t, (s - j) := by
    calc ∏ m ∈ range t, (N - q * (m + 1)) ≤ ∏ m ∈ range t, q * (s - m) :=
          prod_le_prod' hqs
      _ = (∏ _m ∈ range t, q) * ∏ m ∈ range t, (s - m) := by rw [prod_mul_distrib]
      _ = q ^ t * ∏ j ∈ range t, (s - j) := by simp [prod_const, card_range]
  have hch : ∀ n k (_ : k ≤ n), n.choose k * k.factorial = ∏ j ∈ range k, (n - j) := by
    intro n k _
    rw [← descFactorial_eq_prod_range, descFactorial_eq_factorial_mul_choose, mul_comm]
  have hCn := hch N t hNge
  have hCs := hch s t hs_ge
  have hfac : 0 < t.factorial := factorial_pos t
  have : N.choose t * t.factorial ≤ 2 * q ^ t * s.choose t * t.factorial := by
    calc N.choose t * t.factorial = ∏ j ∈ range t, (N - j) := hCn
      _ ≤ N ^ t := hleft
      _ ≤ 2 * ∏ m ∈ range t, (N - q * (m + 1)) := hNt
      _ ≤ 2 * (q ^ t * ∏ j ∈ range t, (s - j)) := Nat.mul_le_mul_left _ hright
      _ = 2 * q ^ t * (s.choose t * t.factorial) := by rw [← hCs]; ring
      _ = 2 * q ^ t * s.choose t * t.factorial := by ring
  exact Nat.le_of_mul_le_mul_right this hfac

/-- **Partition-counting lemma (11).** -/
theorem partition_counting {q : ℕ} [NeZero q] (t N : ℕ) (c : Fin q → ℕ)
    (ht : 1 ≤ t) (hN : q * t * (t + 1) ≤ N) (hsum : ∑ i, c i = N) :
    N.choose t ≤ 2 * q ^ (t - 1) * ∑ i, (c i).choose t := by
  have hq : 0 < q := NeZero.pos q
  have h1 := sum_choose_ge_balanced (q := q) c t N hsum
  have h2 := choose_N_le_two_qpow_choose_s q t N hq ht hN
  have hqpow : q ^ t = q * q ^ (t - 1) := by
    obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 ht)
    rw [pow_succ, Nat.succ_sub_one, mul_comm]
  calc N.choose t ≤ 2 * q ^ t * (N / q).choose t := h2
    _ = 2 * (q * q ^ (t - 1)) * (N / q).choose t := by rw [hqpow]
    _ = 2 * q ^ (t - 1) * (q * (N / q).choose t) := by ring
    _ ≤ 2 * q ^ (t - 1) * ∑ i, (c i).choose t := Nat.mul_le_mul_left _ h1

/-- Index-type form of the partition-counting lemma. -/
theorem partition_counting_fintype {ι : Type*} [Fintype ι] [Nonempty ι]
    (t N : ℕ) (c : ι → ℕ)
    (ht : 1 ≤ t) (hN : Fintype.card ι * t * (t + 1) ≤ N) (hsum : ∑ i, c i = N) :
    N.choose t ≤ 2 * (Fintype.card ι) ^ (t - 1) * ∑ i, (c i).choose t := by
  classical
  let q := Fintype.card ι
  have hq : NeZero q := ⟨Fintype.card_ne_zero⟩
  let e := Fintype.equivFin ι
  -- transport c along e.symm : Fin q → ι
  have hsum' : ∑ i : Fin q, c (e.symm i) = N := by
    rw [← hsum, ← Equiv.sum_comp e.symm]
  have h := partition_counting (q := q) t N (fun i => c (e.symm i)) ht hN hsum'
  have hsum_eq : ∑ i : ι, (c i).choose t = ∑ i : Fin q, (c (e.symm i)).choose t := by
    refine (Equiv.sum_comp e.symm (fun i => (c i).choose t)).symm.trans ?_
    rfl
  simpa [hsum_eq] using h


end E624R7


namespace Erdos624

theorem partition_counting {q : ℕ} [NeZero q] (t N : ℕ) (c : Fin q → ℕ)
    (ht : 1 ≤ t) (hN : q * t * (t + 1) ≤ N) (hsum : ∑ i, c i = N) :
    N.choose t ≤ 2 * q ^ (t - 1) * ∑ i, (c i).choose t :=
  E624R7.partition_counting t N c ht hN hsum

end Erdos624

open Erdos624 in
theorem solution {q : ℕ} [NeZero q] (t N : ℕ) (c : Fin q → ℕ)
    (ht : 1 ≤ t) (hN : q * t * (t + 1) ≤ N) (hsum : ∑ i, c i = N) :
    N.choose t ≤ 2 * q ^ (t - 1) * ∑ i, (c i).choose t :=
  Erdos624.partition_counting t N c ht hN hsum

#print axioms solution

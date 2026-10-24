-- Prove2me | solution 1 for Erdos624.rank_deficiency_labelling
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-24T05:45:27.20793+00:00
-- url     : https://prove2.me/submissions/4db34f8f-9c6d-4801-b994-79d421b2a8d2

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

open Finset Module

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Subset-sum image of labels on `W`. -/
def S_v {k : ℕ} (v : U → Fin k → ZMod 2) (W : Finset U) : Finset (Fin k → ZMod 2) :=
  W.powerset.image (fun A => ∑ x ∈ A, v x)

omit [Fintype U] [DecidableEq U] in
lemma S_v_subset_span {k : ℕ} (v : U → Fin k → ZMod 2) (W : Finset U) :
    (↑(S_v v W) : Set (Fin k → ZMod 2)) ⊆
      (Submodule.span (ZMod 2) (v '' (W : Set U)) : Set _) := by
  intro y hy
  obtain ⟨A, hA, rfl⟩ := by
    simpa [S_v, mem_image, mem_powerset] using hy
  exact Submodule.sum_mem _ fun x hx =>
    Submodule.subset_span (Set.mem_image_of_mem v (hA hx))

lemma card_S_v_le_pow_finrank {k : ℕ} (v : U → Fin k → ZMod 2) (W : Finset U) :
    #(S_v v W) ≤
      2 ^ Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (v '' (W : Set U))) := by
  classical
  set S := Submodule.span (ZMod 2) (v '' (W : Set U))
  let : Fintype S := Fintype.ofFinite _
  have hle : #(S_v v W) ≤ Fintype.card S := by
    let f : S_v v W → S := fun y => ⟨y.1, S_v_subset_span v W y.2⟩
    have hinj : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      change a.val = b.val
      simpa [f] using congr_arg (fun z : S => (z : Fin k → ZMod 2)) h
    simpa using Fintype.card_le_of_injective f hinj
  calc #(S_v v W) ≤ Fintype.card S := hle
    _ = 2 ^ Module.finrank (ZMod 2) S := by
        rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- Extend a subspace up to exact finrank `p`. -/
lemma exists_submodule_finrank_eq {k p : ℕ}
    (S : Submodule (ZMod 2) (Fin k → ZMod 2))
    (hSp : Module.finrank (ZMod 2) S ≤ p) (hp : p ≤ k) :
    ∃ H : Submodule (ZMod 2) (Fin k → ZMod 2),
      S ≤ H ∧ Module.finrank (ZMod 2) H = p := by
  have hV : Module.finrank (ZMod 2) (Fin k → ZMod 2) = k :=
    Module.finrank_fin_fun (R := ZMod 2)
  induction p generalizing S with
  | zero =>
    have : Module.finrank (ZMod 2) S = 0 := by lia
    exact ⟨S, le_rfl, this⟩
  | succ p ih =>
    by_cases hEq : Module.finrank (ZMod 2) S = p + 1
    · exact ⟨S, le_rfl, hEq⟩
    · have hlt : Module.finrank (ZMod 2) S ≤ p := by lia
      obtain ⟨H0, hH0S, hH0⟩ := ih S hlt (by lia)
      by_cases hEq' : Module.finrank (ZMod 2) H0 = p + 1
      · exact ⟨H0, hH0S, hEq'⟩
      · have hltV : Module.finrank (ZMod 2) H0 <
            Module.finrank (ZMod 2) (Fin k → ZMod 2) := by rw [hV, hH0]; lia
        obtain ⟨m, hm⟩ := Submodule.exists_of_finrank_lt H0 hltV
        have hmH : m ∉ H0 := by
          intro h; exact hm (1 : ZMod 2) one_ne_zero (by simpa using h)
        refine ⟨H0 ⊔ Submodule.span (ZMod 2) ({m} : Set _),
          le_trans hH0S le_sup_left, ?_⟩
        rw [Submodule.finrank_sup_span_singleton hmH, hH0]

lemma card_ambient (k : ℕ) : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, Module.finrank_fin_fun]

/-- Coset bound. -/
lemma S_v_coset_bound {k : ℕ} (v : U → Fin k → ZMod 2)
    (H : Submodule (ZMod 2) (Fin k → ZMod 2))
    (B T : Finset U) (z : Fin k → ZMod 2)
    (hBH : Submodule.span (ZMod 2) (v '' (B : Set U)) ≤ H)
    (hT : ∀ x ∈ T, v x - z ∈ H) :
    #(S_v v (B ∪ T)) ≤ 2 ^ (Module.finrank (ZMod 2) H + 1) := by
  classical
  let H' : Submodule (ZMod 2) (Fin k → ZMod 2) :=
    H ⊔ Submodule.span (ZMod 2) ({z} : Set _)
  have hmem : ∀ w ∈ Submodule.span (ZMod 2) (v '' (↑(B ∪ T) : Set U)), w ∈ H' := by
    intro w hw
    refine (Submodule.span_le.2 ?_ : _ ≤ H') hw
    intro y hy
    obtain ⟨x, hxU, rfl⟩ := hy
    have hx : x ∈ B ∪ T := by simpa using hxU
    rcases mem_union.1 hx with hB | hTt
    · exact (le_sup_left : H ≤ H')
        (hBH (Submodule.subset_span (Set.mem_image_of_mem v hB)))
    · have hx' : v x = (v x - z) + z := by abel
      rw [hx']
      exact add_mem ((le_sup_left : H ≤ H') (hT x hTt))
        ((le_sup_right : _ ≤ H') (Submodule.subset_span (Set.mem_singleton z)))
  have hsub : (↑(S_v v (B ∪ T)) : Set _) ⊆ SetLike.coe H' := by
    intro y hy
    have : y ∈ Submodule.span (ZMod 2) (v '' (↑(B ∪ T) : Set U)) :=
      S_v_subset_span v (B ∪ T) hy
    exact hmem y this
  let : Fintype H' := Fintype.ofFinite _
  have hcard : #(S_v v (B ∪ T)) ≤ Fintype.card H' := by
    let f : S_v v (B ∪ T) → H' := fun y => ⟨y.1, hsub y.2⟩
    have hinj : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      change a.val = b.val
      simpa [f] using congr_arg (fun z : H' => (z : Fin k → ZMod 2)) h
    simpa using Fintype.card_le_of_injective f hinj
  have hfr : Module.finrank (ZMod 2) H' ≤ Module.finrank (ZMod 2) H + 1 := by
    have h1 := Submodule.finrank_add_le_finrank_add_finrank H
      (Submodule.span (ZMod 2) ({z} : Set _))
    have h2 : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) ({z} : Set _)) ≤ 1 := by
      by_cases hz : z = 0
      · subst hz
        rw [Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
        exact Nat.zero_le _
      · exact (finrank_span_singleton hz).le
    exact h1.trans (Nat.add_le_add_left h2 _)
  calc #(S_v v (B ∪ T)) ≤ Fintype.card H' := hcard
    _ = 2 ^ Module.finrank (ZMod 2) H' := by
        rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    _ ≤ 2 ^ (Module.finrank (ZMod 2) H + 1) :=
        Nat.pow_le_pow_right (by decide : (0 : ℕ) < 2) hfr

/-- For k≥16, 2^k-(k-9) ≥ 512·7·8. -/
lemma large_remaining (k : ℕ) (hk : 16 ≤ k) :
    512 * 7 * 8 ≤ 2 ^ k - (k - 9) := by
  have hmain : 512 * 7 * 8 + (k - 9) ≤ 2 ^ k := by
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      have hrewrite : (n + 1) - 9 = (n - 9) + 1 := by lia
      calc 512 * 7 * 8 + ((n + 1) - 9)
          = 512 * 7 * 8 + (n - 9) + 1 := by rw [hrewrite]; ring
        _ ≤ 2 ^ n + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left (by lia : 1 ≤ 2 ^ n) _
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring
  exact Nat.le_sub_of_add_le hmain

/-- Fiber-sum: ∑_y #{x ∈ s | f x = y} = #s. -/
lemma sum_card_fibers {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    (s : Finset α) (f : α → β) :
    ∑ y : β, #{x ∈ s | f x = y} = #s := by
  classical
  have h := sum_fiberwise (s := s) (g := f) (fun _ : α => (1 : ℕ))
  simp only [sum_const, smul_eq_mul, mul_one] at h
  simpa using h



/-- Quotient by a `p`-dimensional subspace of `F₂^k` has cardinality `2^(k-p)`. -/
lemma card_quotient_of_finrank {k p : ℕ}
    (H : Submodule (ZMod 2) (Fin k → ZMod 2))
    (hH : Module.finrank (ZMod 2) H = p) (_hp : p ≤ k) :
    Fintype.card ((Fin k → ZMod 2) ⧸ H) = 2 ^ (k - p) := by
  have hV : Module.finrank (ZMod 2) (Fin k → ZMod 2) = k :=
    Module.finrank_fin_fun (R := ZMod 2)
  have hsum := Submodule.finrank_quotient_add_finrank (R := ZMod 2) H
  have hQ : Module.finrank (ZMod 2) ((Fin k → ZMod 2) ⧸ H) = k - p := by lia
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hQ]

/-- Good-completions (5). -/
lemma good_completions {k : ℕ} (hk : 16 ≤ k)
    (hU : Fintype.card U = 2 ^ k) (v : U → Fin k → ZMod 2)
    (B : Finset U) (hB : #B = k - 9) :
    Nat.choose (2 ^ k - (k - 9)) 7 ≤
      2 ^ 55 *
        #{T ∈ powersetCard 7 (univ \ B) |
          256 * #(S_v v (B ∪ T)) ≤ 2 ^ k} := by
  classical
  set p := k - 9
  set n := 2 ^ k
  set S := Submodule.span (ZMod 2) (v '' (B : Set U))
  have hSfr : Module.finrank (ZMod 2) S ≤ p := by
    have heq : S = Submodule.span (ZMod 2) ↑(B.image v) := by
      simp only [S]; rw [Finset.coe_image]
    rw [heq]
    refine (finrank_span_finset_le_card (R := ZMod 2) (B.image v)).trans ?_
    exact card_image_le.trans (hB.symm ▸ le_rfl)
  obtain ⟨H, hHS, hHfr⟩ := exists_submodule_finrank_eq S hSfr (by lia : p ≤ k)
  have hQcard : Fintype.card ((Fin k → ZMod 2) ⧸ H) = 2 ^ 9 := by
    rw [card_quotient_of_finrank H hHfr (by lia)]
    congr 1; lia
  let Q := (Fin k → ZMod 2) ⧸ H
  let fiber : Q → Finset U := fun q =>
    (univ \ B).filter (fun x => H.mkQ (v x) = q)
  let c : Q → ℕ := fun q => #(fiber q)
  have hsumc : ∑ q, c q = n - p := by
    have hf := sum_card_fibers (univ \ B) (fun x => H.mkQ (v x))
    have hcard : #(univ \ B) = n - p := by
      rw [card_sdiff_of_subset (subset_univ _), Finset.card_univ, hU, hB]
    exact hf.trans hcard
  have hNbound : Fintype.card Q * 7 * 8 ≤ n - p := by
    rw [hQcard]; simpa [n, p] using large_remaining k hk
  have : Nonempty Q :=
    ⟨Classical.choice (Fintype.card_pos_iff.mp (by rw [hQcard]; norm_num))⟩
  have hpart :=
    partition_counting_fintype (ι := Q) 7 (n - p) c (by norm_num) hNbound hsumc
  have h255 : 2 * (Fintype.card Q) ^ (7 - 1) = 2 ^ 55 := by
    rw [hQcard]; norm_num
  let goodT : Finset (Finset U) :=
    (powersetCard 7 (univ \ B)).filter
      (fun T => 256 * #(S_v v (B ∪ T)) ≤ 2 ^ k)
  have hfiber_good : ∀ q, powersetCard 7 (fiber q) ⊆ goodT := by
    intro q T hT
    have ⟨hTsub, hTcard⟩ := mem_powersetCard.1 hT
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective H q
    have hTcoset : ∀ x ∈ T, v x - z ∈ H := by
      intro x hx
      have hxF : x ∈ fiber (H.mkQ z) := hTsub hx
      have hxEq : H.mkQ (v x) = H.mkQ z := (mem_filter.mp hxF).2
      exact (Submodule.Quotient.eq H).1 hxEq
    have hbound := S_v_coset_bound v H B T z hHS hTcoset
    rw [hHfr] at hbound
    have hmul := Nat.mul_le_mul_left 256 hbound
    have hpow : 256 * 2 ^ (p + 1) = 2 ^ k := by
      have hp1 : p + 1 = k - 8 := by lia
      rw [hp1, show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_add]
      congr 1; lia
    exact mem_filter.2
      ⟨mem_powersetCard.2 ⟨hTsub.trans (filter_subset _ _), hTcard⟩,
        hmul.trans (le_of_eq hpow)⟩
  have hsum_le : ∑ q, (c q).choose 7 ≤ #goodT := by
    have hcardf : ∀ q, #(powersetCard 7 (fiber q)) = (c q).choose 7 := fun q =>
      card_powersetCard _ _
    have hdisj : ∀ q ∈ (univ : Finset Q), ∀ q' ∈ univ, q ≠ q' →
        Disjoint (powersetCard 7 (fiber q)) (powersetCard 7 (fiber q')) := by
      intro q _ q' _ hne
      refine disjoint_left.2 fun T hT hT' => ?_
      have ⟨hTs, hTc⟩ := mem_powersetCard.1 hT
      have ⟨hTs', _⟩ := mem_powersetCard.1 hT'
      have hne7 : T.Nonempty := card_pos.mp (by rw [hTc]; norm_num)
      obtain ⟨x, hx⟩ := hne7
      exact hne <|
        ((mem_filter.1 (hTs hx)).2).symm.trans (mem_filter.1 (hTs' hx)).2
    have hunion_sub :
        ((univ : Finset Q).biUnion fun q => powersetCard 7 (fiber q)) ⊆ goodT := by
      intro T hT
      obtain ⟨q, _, hq⟩ := mem_biUnion.1 hT
      exact hfiber_good q hq
    calc ∑ q, (c q).choose 7
        = ∑ q, #(powersetCard 7 (fiber q)) := by simp [hcardf]
      _ = #((univ : Finset Q).biUnion fun q => powersetCard 7 (fiber q)) :=
          (card_biUnion hdisj).symm
      _ ≤ #goodT := card_le_card hunion_sub
  change Nat.choose (n - p) 7 ≤ 2 ^ 55 * #goodT
  calc Nat.choose (n - p) 7
      ≤ 2 * (Fintype.card Q) ^ (7 - 1) * ∑ q, (c q).choose 7 := hpart
    _ = 2 ^ 55 * ∑ q, (c q).choose 7 := by rw [h255]
    _ ≤ 2 ^ 55 * #goodT := Nat.mul_le_mul_left (2 ^ 55) hsum_le

/-- The rank-deficiency labelling lemma (10)/(21). -/
theorem rank_deficiency_labelling {k : ℕ} (hk : 16 ≤ k)
    (hU : Fintype.card U = 2 ^ k) (v : U → Fin k → ZMod 2) :
    Nat.choose (2 ^ k) (k - 2) ≤
      2 ^ 55 *
        #{W ∈ powersetCard (k - 2) (univ : Finset U) |
          256 * #(S_v v W) ≤ 2 ^ k} := by
  classical
  set p := k - 9
  set m := k - 2
  set n := 2 ^ k
  have hm : m = p + 7 := by lia
  have hpm : p ≤ m := by lia
  let good : Finset (Finset U) :=
    (powersetCard m univ).filter (fun W => 256 * #(S_v v W) ≤ 2 ^ k)
  let a (B : Finset U) : ℕ :=
    #{T ∈ powersetCard 7 (univ \ B) | 256 * #(S_v v (B ∪ T)) ≤ 2 ^ k}
  have hgc : ∀ B ∈ powersetCard p (univ : Finset U),
      Nat.choose (n - p) 7 ≤ 2 ^ 55 * a B := by
    intro B hB
    simpa [a, n, p] using
      good_completions hk hU v B (mem_powersetCard.1 hB).2
  have hsum : Nat.choose n p * Nat.choose (n - p) 7 ≤
      2 ^ 55 * ∑ B ∈ powersetCard p univ, a B := by
    have h := sum_le_sum hgc
    have hL : ∑ B ∈ powersetCard p (univ : Finset U), Nat.choose (n - p) 7 =
        Nat.choose n p * Nat.choose (n - p) 7 := by
      have hc : #(powersetCard p (univ : Finset U)) = Nat.choose n p := by
        rw [card_powersetCard, Finset.card_univ (α := U), hU]
      rw [sum_const, hc, nsmul_eq_mul, Nat.cast_id]
    have hR0 : ∑ B ∈ powersetCard p univ, 2 ^ 55 * a B =
        2 ^ 55 * ∑ B ∈ powersetCard p univ, a B := by rw [← mul_sum]
    rw [← hL, ← hR0]; exact h
  have hR : ∑ B ∈ powersetCard p univ, a B = #good * Nat.choose m p := by
    let Left := (powersetCard p univ).sigma fun B =>
      (powersetCard 7 (univ \ B)).filter
        (fun T => 256 * #(S_v v (B ∪ T)) ≤ 2 ^ k)
    let Right := good.sigma fun W => powersetCard p W
    have hcardL : ∑ B ∈ powersetCard p univ, a B = ∑ x ∈ Left, (1 : ℕ) := by
      simp only [Left, a, sum_sigma, card_eq_sum_ones]
    have hcardR : ∑ x ∈ Right, (1 : ℕ) = #good * Nat.choose m p := by
      dsimp only [Right]
      rw [sum_sigma]
      have h1 : ∀ W ∈ good, ∑ _B ∈ powersetCard p W, (1 : ℕ) = Nat.choose m p := by
        intro W hW
        rw [← card_eq_sum_ones, card_powersetCard]
        exact congrArg (fun n => Nat.choose n p)
          (mem_powersetCard.1 (mem_filter.1 hW).1).2
      rw [sum_congr rfl h1, sum_const, nsmul_eq_mul, Nat.cast_id]
    have hbij : ∑ x ∈ Left, (1 : ℕ) = ∑ x ∈ Right, (1 : ℕ) := by
      refine sum_nbij'
        (fun σ => ⟨σ.1 ∪ σ.2, σ.1⟩)
        (fun τ => ⟨τ.2, τ.1 \ τ.2⟩)
        ?hi ?hj ?linv ?rinv (fun _ _ => rfl)
      · intro ⟨B, T⟩ hBT
        simp only [Left, mem_sigma, mem_filter, mem_powersetCard, Right, good] at hBT ⊢
        obtain ⟨⟨hBsub, hBcard⟩, ⟨⟨hTsub, hTcard⟩, hgood⟩⟩ := hBT
        have hdisj : Disjoint B T :=
          disjoint_left.2 fun _ hxB hxT => (mem_sdiff.1 (hTsub hxT)).2 hxB
        have hWcard : #(B ∪ T) = m := by
          rw [card_union_of_disjoint hdisj, hBcard, hTcard, hm]
        exact ⟨⟨⟨subset_univ _, hWcard⟩, hgood⟩, ⟨subset_union_left, hBcard⟩⟩
      · intro ⟨W, B⟩ hWB
        simp only [Right, mem_sigma, mem_filter, mem_powersetCard, Left, good] at hWB ⊢
        obtain ⟨⟨⟨hWsub, hWcard⟩, hWgood⟩, ⟨hBsub, hBcard⟩⟩ := hWB
        have hTcard : #(W \ B) = 7 := by
          rw [card_sdiff_of_subset hBsub, hWcard, hBcard]; lia
        have hTsub : W \ B ⊆ univ \ B := fun x hx => by
          simp only [mem_sdiff] at hx ⊢; exact ⟨mem_univ _, hx.2⟩
        have hBun : B ∪ (W \ B) = W := union_sdiff_of_subset hBsub
        refine ⟨⟨subset_univ _, hBcard⟩, ⟨⟨hTsub, hTcard⟩, ?_⟩⟩
        simpa [hBun] using hWgood
      · intro ⟨B, T⟩ hBT
        simp only [Left, mem_sigma, mem_filter, mem_powersetCard] at hBT
        obtain ⟨⟨_, _⟩, ⟨⟨hTsub, _⟩, _⟩⟩ := hBT
        have hdisj : Disjoint B T :=
          disjoint_left.2 fun _ hxB hxT => (mem_sdiff.1 (hTsub hxT)).2 hxB
        refine Sigma.ext rfl (heq_of_eq (union_sdiff_cancel_left hdisj))
      · intro ⟨W, B⟩ hWB
        simp only [Right, mem_sigma, mem_filter, mem_powersetCard, good] at hWB
        obtain ⟨⟨⟨_, _⟩, _⟩, ⟨hBsub, _⟩⟩ := hWB
        refine Sigma.ext (union_sdiff_of_subset hBsub) (heq_of_eq rfl)
    exact hcardL.trans (hbij.trans hcardR)
  have hid : Nat.choose n m * Nat.choose m p =
      Nat.choose n p * Nat.choose (n - p) 7 := by
    simpa [show m - p = 7 by lia] using
      Nat.choose_mul (n := n) (k := m) (s := p) hpm
  have hpos : 0 < Nat.choose m p := Nat.choose_pos hpm
  have : Nat.choose n m * Nat.choose m p ≤ 2 ^ 55 * #good * Nat.choose m p := by
    calc Nat.choose n m * Nat.choose m p
        = Nat.choose n p * Nat.choose (n - p) 7 := hid
      _ ≤ 2 ^ 55 * ∑ B ∈ powersetCard p univ, a B := hsum
      _ = 2 ^ 55 * (#good * Nat.choose m p) := by rw [hR]
      _ = 2 ^ 55 * #good * Nat.choose m p := by ring
  have := Nat.le_of_mul_le_mul_right this hpos
  simpa [good, n, m] using this

end E624R7


namespace Erdos624
open Finset

/-- **Rank-deficiency labelling lemma (10)/(21).**
`S_v(W)` is written inline as the powerset-image of subset-sums. -/
theorem rank_deficiency_labelling {U : Type*} [Fintype U] [DecidableEq U]
    {k : ℕ} (hk : 16 ≤ k)
    (hU : Fintype.card U = 2 ^ k) (v : U → Fin k → ZMod 2) :
    Nat.choose (2 ^ k) (k - 2) ≤
      2 ^ 55 *
        #{W ∈ powersetCard (k - 2) (univ : Finset U) |
          256 * #(W.powerset.image (fun A => ∑ x ∈ A, v x)) ≤ 2 ^ k} := by
  classical
  convert E624R7.rank_deficiency_labelling (U := U) hk hU v
  · rfl

end Erdos624

open Finset

theorem solution {U : Type*} [Fintype U] [DecidableEq U]
    {k : ℕ} (hk : 16 ≤ k)
    (hU : Fintype.card U = 2 ^ k) (v : U → Fin k → ZMod 2) :
    Nat.choose (2 ^ k) (k - 2) ≤
      2 ^ 55 *
        #{W ∈ powersetCard (k - 2) (univ : Finset U) |
          256 * #(W.powerset.image (fun A => ∑ x ∈ A, v x)) ≤ 2 ^ k} :=
  Erdos624.rank_deficiency_labelling hk hU v

#print axioms solution
#print axioms Erdos624.rank_deficiency_labelling

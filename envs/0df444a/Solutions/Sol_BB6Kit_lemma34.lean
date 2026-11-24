-- Prove2me | solution 1 for BB6Kit.lemma34
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-24T07:40:43.679138+00:00
-- url     : https://prove2.me/submissions/1a5da623-8449-4e0c-addc-c01292e09fe1

import Mathlib
import Definitions.Def_BB6Theta

open Finset

namespace L34

lemma gauss (L : ℕ) : ∑ v ∈ range L, (v : ℝ) = (L : ℝ) * ((L : ℝ) - 1) / 2 := by
  induction L with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

lemma sqsum (K : ℕ) : ∑ v ∈ range K, (v : ℝ) ^ 2 = (K : ℝ) * ((K : ℝ) - 1) * (2 * (K : ℝ) - 1) / 6 := by
  induction K with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

lemma tri_sum (q : ℕ) : ∑ v ∈ range q, ((q - v : ℕ) : ℝ) = (q:ℝ) * ((q:ℝ) + 1) / 2 := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h : ∑ v ∈ range n, ((n + 1 - v : ℕ) : ℝ) = ∑ v ∈ range n, (((n - v : ℕ) : ℝ) + 1) := by
      apply sum_congr rfl
      intro v hv
      rw [mem_range] at hv
      rw [show n + 1 - v = (n - v) + 1 by omega, Nat.cast_add, Nat.cast_one]
    rw [h, sum_add_distrib, ih, show n + 1 - n = 1 by omega]
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
    push_cast
    ring

lemma theta_mem (K0 I : ℕ) : ∃ P : Finset (ℕ × ℕ), P.card = I ∧ (∀ p ∈ P, p.2 ≤ K0) ∧
    BB6Theta.theta K0 I = ∑ p ∈ P, (p.1 + p.2) := by
  have hne : {s : ℕ | ∃ P : Finset (ℕ × ℕ), P.card = I ∧ (∀ p ∈ P, p.2 ≤ K0) ∧
      s = ∑ p ∈ P, (p.1 + p.2)}.Nonempty := by
    refine ⟨_, (range I).image (fun k => (k, 0)), ?_, ?_, rfl⟩
    · rw [card_image_of_injective _ (fun a b h => by simpa using h), card_range]
    · intro p hp
      rw [mem_image] at hp
      obtain ⟨k, _, rfl⟩ := hp
      simp
  obtain ⟨P, h1, h2, h3⟩ := Nat.sInf_mem hne
  exact ⟨P, h1, h2, h3⟩

lemma theta_le (K0 I : ℕ) (P : Finset (ℕ × ℕ)) (hP : P.card = I) (hm : ∀ p ∈ P, p.2 ≤ K0) :
    BB6Theta.theta K0 I ≤ ∑ p ∈ P, (p.1 + p.2) :=
  Nat.sInf_le ⟨P, hP, hm, rfl⟩

lemma inner_T (q m : ℕ) (hm : m ≤ q) :
    ∑ k ∈ range q, ((q - m - k : ℕ) : ℝ) = ((q - m : ℕ) : ℝ) * (((q - m : ℕ) : ℝ) + 1) / 2 := by
  rw [← tri_sum (q - m), ← sum_range_add_sum_Ico _ (show q - m ≤ q by omega)]
  have : ∑ k ∈ Ico (q - m) q, ((q - m - k : ℕ) : ℝ) = 0 := by
    apply sum_eq_zero
    intro k hk
    rw [mem_Ico] at hk
    rw [show q - m - k = 0 by omega, Nat.cast_zero]
  rw [this, add_zero]

/-- Pointwise threshold bound: the degrees of `|P|` pairs with `m ≤ K0` sum to at least `q|P| - V(q)`. -/
lemma lower (K0 q : ℕ) (P : Finset (ℕ × ℕ)) (hm : ∀ p ∈ P, p.2 ≤ K0) :
    (q : ℝ) * P.card - ∑ m ∈ range (K0 + 1), ∑ k ∈ range q, ((q - m - k : ℕ) : ℝ) ≤
      ∑ p ∈ P, ((p.1 + p.2 : ℕ) : ℝ) := by
  have hpt : ∀ p ∈ P, (q : ℝ) - ((q - (p.1 + p.2) : ℕ) : ℝ) ≤ ((p.1 + p.2 : ℕ) : ℝ) := by
    intro p _
    rcases le_total (p.1 + p.2) q with h | h
    · rw [Nat.cast_sub h]; linarith
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, sub_zero]; exact_mod_cast h
  have h1 := sum_le_sum hpt
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul] at h1
  have h2 : ∑ p ∈ P, ((q - (p.1 + p.2) : ℕ) : ℝ) ≤
      ∑ m ∈ range (K0 + 1), ∑ k ∈ range q, ((q - m - k : ℕ) : ℝ) := by
    calc ∑ p ∈ P, ((q - (p.1 + p.2) : ℕ) : ℝ)
        = ∑ p ∈ P.filter (fun p => p.1 + p.2 < q), ((q - (p.1 + p.2) : ℕ) : ℝ) := by
          rw [sum_filter]
          apply sum_congr rfl
          intro p _
          split_ifs with h
          · rfl
          · rw [show q - (p.1 + p.2) = 0 by omega, Nat.cast_zero]
      _ ≤ ∑ p ∈ range q ×ˢ range (K0 + 1), ((q - (p.1 + p.2) : ℕ) : ℝ) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro p hp
            rw [mem_filter] at hp
            have := hm p hp.1
            simp only [mem_product, mem_range]
            omega
          · intro p _ _
            exact Nat.cast_nonneg _
      _ = ∑ k ∈ range q, ∑ m ∈ range (K0 + 1), ((q - (k + m) : ℕ) : ℝ) := sum_product _ _ _
      _ = ∑ m ∈ range (K0 + 1), ∑ k ∈ range q, ((q - m - k : ℕ) : ℝ) := by
          rw [sum_comm]
          apply sum_congr rfl
          intro m _
          apply sum_congr rfl
          intro k _
          rw [show q - (k + m) = q - m - k by omega]
  linarith

end L34

theorem solution (K L N I : ℕ) (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hI : I ≤ N) :
    (N : ℝ) ^ 2 / (2 * (K : ℝ)) * (1 + 2 / (L : ℝ) - 6 / ((K : ℝ) * L) - 1 / (3 * (L : ℝ) ^ 2)) ≤
      (K : ℝ) * L * ((N : ℝ) - I) + (BB6Theta.theta (K - 1) I : ℝ) := by
  have hKr : (3:ℝ) ≤ K := by exact_mod_cast hK
  have hLr : (5:ℝ) ≤ L := by exact_mod_cast hL
  have hNA : (N:ℝ) = ((K:ℝ) * ((K:ℝ) + 1) / 2) * L := by
    have hdvd : 2 ∣ K * (K + 1) * L := (Nat.even_mul_succ_self K).two_dvd.mul_right L
    rw [hN, Nat.cast_div hdvd (by norm_num : ((2:ℕ):ℝ) ≠ 0)]
    push_cast
    ring
  -- Step (a): Θ(K-1, N) ≤ Θ(K-1, I) + (N - I) K L
  have hstepA : BB6Theta.theta (K - 1) N ≤ BB6Theta.theta (K - 1) I + (N - I) * (K * L) := by
    obtain ⟨P, hPc, hPm, hPs⟩ := L34.theta_mem (K - 1) I
    set Q : Finset (ℕ × ℕ) := range (K * L - K + 1) ×ˢ range K with hQ
    have hQc : N ≤ Q.card := by
      rw [hQ, card_product, card_range, card_range, hN]
      have h1 : K * (K + 1) * L ≤ 2 * ((K * L - K + 1) * K) := by
        have : K ≤ K * L := Nat.le_mul_of_pos_right K (by omega)
        have e : (K * L - K + 1) * K = K * L * K - K * K + K := by
          rw [Nat.add_mul, Nat.sub_mul, one_mul]
        rw [e]
        have h2 : K * K ≤ K * L * K := Nat.mul_le_mul_right K this
        have h3 : (K - 1) * (L - 2) ≥ 2 := by
          have : 2 ≤ K - 1 := by omega
          have : 3 ≤ L - 2 := by omega
          nlinarith
        zify [h2, this, show 1 ≤ K by omega, show 2 ≤ L by omega] at h3 ⊢
        nlinarith
      omega
    have hsd : N - I ≤ (Q \ P).card := by
      have := le_card_sdiff P Q
      omega
    obtain ⟨E, hEsub, hEc⟩ : ∃ E ⊆ Q \ P, E.card = N - I := by
      have hpos : 0 < (powersetCard (N - I) (Q \ P)).card := by
        rw [card_powersetCard]
        exact Nat.choose_pos hsd
      obtain ⟨E, hE⟩ := card_pos.mp hpos
      rw [mem_powersetCard] at hE
      exact ⟨E, hE.1, hE.2⟩
    have hdisj : Disjoint P E := by
      rw [disjoint_left]
      intro p hp hpE
      have := hEsub hpE
      rw [mem_sdiff] at this
      exact this.2 hp
    have hcard : (P ∪ E).card = N := by
      rw [card_union_of_disjoint hdisj, hPc, hEc]
      omega
    have hm : ∀ p ∈ P ∪ E, p.2 ≤ K - 1 := by
      intro p hp
      rw [mem_union] at hp
      rcases hp with hp | hp
      · exact hPm p hp
      · have := hEsub hp
        rw [mem_sdiff, hQ, mem_product, mem_range, mem_range] at this
        omega
    have hle := L34.theta_le (K - 1) N (P ∪ E) hcard hm
    rw [sum_union hdisj, ← hPs] at hle
    have hEs : ∑ p ∈ E, (p.1 + p.2) ≤ ∑ p ∈ E, (K * L) := by
      apply sum_le_sum
      intro p hp
      have := hEsub hp
      rw [mem_sdiff, hQ, mem_product, mem_range, mem_range] at this
      have : K ≤ K * L := Nat.le_mul_of_pos_right K (by omega)
      omega
    rw [sum_const, hEc, smul_eq_mul] at hEs
    omega
  -- Step (b): W ≤ Θ(K-1, N) via the threshold q
  have hstepB : (N : ℝ) ^ 2 / (2 * (K : ℝ)) * (1 + 2 / (L : ℝ) - 6 / ((K : ℝ) * L) - 1 / (3 * (L : ℝ) ^ 2)) ≤
      (BB6Theta.theta (K - 1) N : ℝ) := by
    obtain ⟨P, hPc, hPm, hPs⟩ := L34.theta_mem (K - 1) N
    set q : ℕ := ((K + 1) * L + K - 2) / 2 with hq
    have hlow := L34.lower (K - 1) q P hPm
    rw [hPc, show K - 1 + 1 = K by omega] at hlow
    have hqK : K - 1 ≤ q := by
      rw [hq]
      have : K ≤ (K + 1) * L := by nlinarith
      omega
    have hV : ∑ m ∈ range K, ∑ k ∈ range q, ((q - m - k : ℕ) : ℝ) =
        ((K : ℝ) * (q : ℝ) ^ 2 + K * q - (2 * q + 1) * (K * ((K : ℝ) - 1) / 2) +
          (K : ℝ) * ((K : ℝ) - 1) * (2 * K - 1) / 6) / 2 := by
      have e : ∀ m ∈ range K, ∑ k ∈ range q, ((q - m - k : ℕ) : ℝ) =
          ((q : ℝ) ^ 2 + q - (2 * q + 1) * m + (m : ℝ) ^ 2) / 2 := by
        intro m hm
        rw [mem_range] at hm
        rw [L34.inner_T q m (by omega), Nat.cast_sub (by omega)]
        ring
      rw [sum_congr rfl e, ← sum_div, sum_add_distrib, sum_sub_distrib, sum_add_distrib, sum_const, card_range,
        nsmul_eq_mul, ← mul_sum, L34.gauss, L34.sqsum]
      try simp only [sum_const, card_range, nsmul_eq_mul]
      try push_cast
      try ring
    rw [hV] at hlow
    have hsum : (BB6Theta.theta (K - 1) N : ℝ) = ∑ p ∈ P, ((p.1 + p.2 : ℕ) : ℝ) := by
      rw [hPs]; push_cast; rfl
    rw [hsum]
    refine le_trans ?_ hlow
    -- polynomial inequality in K, L, q
    have hq1 : 2 * q ≤ (K + 1) * L + K - 2 := by rw [hq]; omega
    have hq2 : (K + 1) * L + K - 2 ≤ 2 * q + 1 := by rw [hq]; omega
    have hA : (((K + 1) * L + K - 2 : ℕ) : ℝ) = ((K : ℝ) + 1) * L + K - 2 := by
      have : 2 ≤ (K + 1) * L + K := by nlinarith
      rw [Nat.cast_sub this]
      push_cast
      ring
    have hq1r : 2 * (q : ℝ) ≤ ((K : ℝ) + 1) * L + K - 2 := by
      rw [← hA]; exact_mod_cast hq1
    have hq2r : ((K : ℝ) + 1) * L + K - 2 ≤ 2 * (q : ℝ) + 1 := by
      rw [← hA]; exact_mod_cast hq2
    have hd : (((K : ℝ) + 1) * L + K - 2 - 2 * q) ^ 2 ≤ 1 := by nlinarith
    have hKpos : (0 : ℝ) < K := by linarith
    have hLpos : (0 : ℝ) < L := by linarith
    have iden : (q : ℝ) * N - ((K : ℝ) * (q : ℝ) ^ 2 + K * q - (2 * q + 1) * (K * ((K : ℝ) - 1) / 2) +
          (K : ℝ) * ((K : ℝ) - 1) * (2 * K - 1) / 6) / 2 -
        (N : ℝ) ^ 2 / (2 * (K : ℝ)) * (1 + 2 / (L : ℝ) - 6 / ((K : ℝ) * L) - 1 / (3 * (L : ℝ) ^ 2)) =
        3 * ((K : ℝ) + 1) * L / 4 + K * (2 * K + 5) / 24 -
          K / 8 * (((K : ℝ) + 1) * L + K - 2 - 2 * q) ^ 2 := by
      rw [hNA]
      field_simp
      ring
    have hd2 : K / 8 * (((K : ℝ) + 1) * L + K - 2 - 2 * q) ^ 2 ≤ K / 8 :=
      mul_le_of_le_one_right (by positivity) hd
    have hpos : (0:ℝ) ≤ 3 * ((K : ℝ) + 1) * L / 4 + K * (2 * K + 5) / 24 - K / 8 := by nlinarith
    linarith [iden, hd2, hpos]
  -- combine
  have hA' : ((BB6Theta.theta (K - 1) N : ℕ) : ℝ) ≤ (BB6Theta.theta (K - 1) I : ℝ) + ((N - I : ℕ) : ℝ) * ((K : ℝ) * L) := by
    exact_mod_cast hstepA
  rw [Nat.cast_sub hI] at hA'
  linarith [hstepB, hA']

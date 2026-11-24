-- Prove2me | solution 1 for BB6Kit.rows_counts
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-24T07:31:38.470799+00:00
-- url     : https://prove2.me/submissions/05991005-702d-4da7-ae97-548b61a874ab

import Mathlib
import Definitions.Def_BB6Kit

open Finset

namespace RC

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

/-- Count of `m < K` with `k + m ≤ K - 1`, weighted by `L`. -/
lemma inner_count (K L k : ℕ) (hk : k < K) (c : ℝ) :
    ∑ m ∈ range K, ∑ v ∈ range L, (if k + m ≤ K - 1 then c else 0) = (L : ℝ) * (((K - k : ℕ) : ℝ) * c) := by
  have h : ∀ m ∈ range K, ∑ v ∈ range L, (if k + m ≤ K - 1 then c else 0) =
      (if m < K - k then (L : ℝ) * c else 0) := by
    intro m hm
    rw [mem_range] at hm
    by_cases hc : m < K - k
    · rw [if_pos hc, sum_congr rfl (fun v _ => if_pos (show k + m ≤ K - 1 by omega))]
      simp
    · rw [if_neg hc]
      apply sum_eq_zero
      intro v _
      rw [if_neg (show ¬ (k + m ≤ K - 1) by omega)]
  rw [sum_congr rfl h, ← sum_filter, sum_const]
  have hf : (range K).filter (fun m => m < K - k) = range (K - k) := by
    ext m
    simp only [mem_filter, mem_range]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨by omega, h⟩
  rw [hf, card_range, nsmul_eq_mul]
  ring

lemma sum_k (K L : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ BB6Kit.rowSet K L, f p.1 = (L : ℝ) * ∑ k ∈ range K, ((K - k : ℕ) : ℝ) * f k := by
  unfold BB6Kit.rowSet
  rw [sum_filter]
  simp only [sum_product]
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  exact inner_count K L k (mem_range.mp hk) (f k)

lemma sum_m (K L : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ BB6Kit.rowSet K L, f p.2.1 = (L : ℝ) * ∑ m ∈ range K, ((K - m : ℕ) : ℝ) * f m := by
  unfold BB6Kit.rowSet
  rw [sum_filter]
  simp only [sum_product]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro m hm
  have := inner_count K L m (mem_range.mp hm) (f m)
  rw [← this]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro v _
  rw [add_comm k m]

lemma weighted_id (K : ℕ) :
    ∑ k ∈ range K, ((K - k : ℕ) : ℝ) * (k : ℝ) = (K : ℝ) * ((K : ℝ) - 1) * ((K : ℝ) + 1) / 6 := by
  have h : ∀ k ∈ range K, ((K - k : ℕ) : ℝ) * (k : ℝ) = (K : ℝ) * k - (k : ℝ) ^ 2 := by
    intro k hk
    rw [Nat.cast_sub (mem_range.mp hk).le]
    ring
  rw [sum_congr rfl h, sum_sub_distrib, ← mul_sum, gauss, sqsum]
  ring

end RC

theorem solution (K L N : ℕ) (kml : Fin N → ℕ × ℕ × ℕ) (hK : 3 ≤ K) (hL : 5 ≤ L)
    (hN : N = K * (K + 1) * L / 2) (hrows : BB6Kit.RowsOK K L N kml) :
    (∑ i, ((kml i).1 : ℝ)) = (N : ℝ) * ((K : ℝ) - 1) / 3 ∧
    (∑ i, ((kml i).2.1 : ℝ)) = (N : ℝ) * ((K : ℝ) - 1) / 3 ∧
    ∑ i, (Real.log ((kml i).1.factorial : ℝ) + Real.log ((kml i).2.1.factorial : ℝ)) =
      2 * (L : ℝ) * Real.log (∏ k ∈ Finset.Ico 1 K, ((k.factorial : ℝ) ^ (K - k))) := by
  have hNA : (N:ℝ) = ((K:ℝ) * ((K:ℝ) + 1) / 2) * L := by
    have hdvd : 2 ∣ K * (K + 1) * L := (Nat.even_mul_succ_self K).two_dvd.mul_right L
    rw [hN, Nat.cast_div hdvd (by norm_num : ((2:ℕ):ℝ) ≠ 0)]
    push_cast
    ring
  -- the rows enumerate the row set
  have hcardR : ((BB6Kit.rowSet K L).card : ℝ) = N := by
    rw [hNA, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    rw [RC.sum_k K L (fun _ => (1:ℝ))]
    simp only [mul_one]
    rw [RC.tri_sum K]
    ring
  have hcard : (BB6Kit.rowSet K L).card = N := by exact_mod_cast hcardR
  have himg : univ.image kml = BB6Kit.rowSet K L := by
    apply eq_of_subset_of_card_le
    · intro p hp
      rw [mem_image] at hp
      obtain ⟨i, _, rfl⟩ := hp
      exact hrows.2 i
    · rw [card_image_of_injective _ hrows.1, card_univ, Fintype.card_fin, hcard]
  have hsum : ∀ F : ℕ × ℕ × ℕ → ℝ, ∑ i, F (kml i) = ∑ p ∈ BB6Kit.rowSet K L, F p := by
    intro F
    rw [← himg, sum_image (by intro x _ y _ h; exact hrows.1 h)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum (fun p => (p.1 : ℝ)), RC.sum_k K L (fun k => (k : ℝ)), RC.weighted_id, hNA]
    ring
  · rw [hsum (fun p => (p.2.1 : ℝ)), RC.sum_m K L (fun k => (k : ℝ)), RC.weighted_id, hNA]
    ring
  · rw [hsum (fun p => Real.log (p.1.factorial : ℝ) + Real.log (p.2.1.factorial : ℝ)), sum_add_distrib,
      RC.sum_k K L (fun k => Real.log (k.factorial : ℝ)), RC.sum_m K L (fun k => Real.log (k.factorial : ℝ))]
    rw [Real.log_prod (fun k _ => by have := Nat.factorial_pos k; positivity)]
    have hK0 : 0 < K := by omega
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hK0]
    simp only [Nat.factorial_zero, Nat.cast_one, Real.log_one, mul_zero, zero_add, Real.log_pow]
    ring

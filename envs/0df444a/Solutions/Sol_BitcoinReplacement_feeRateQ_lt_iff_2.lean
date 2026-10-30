-- Prove2me | solution 2 for BitcoinReplacement.feeRateQ_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:32:14.184208+00:00
-- url     : https://prove2.me/submissions/91acaebc-b8c3-4c9d-97d6-d470c197c169

import Definitions.Def_BitcoinReplacement

open BitcoinReplacement

/-- `GetFee v ≤ n` iff `fee · v ≤ n · size`: `getFee` is the least `n` with `fee·v ≤ n·size`. -/
private theorem getFee_le_iff (r : FeeRate) (v n : ℕ) :
    r.getFee v ≤ n ↔ r.fee * v ≤ n * r.size := by
  unfold FeeRate.getFee
  have hs := r.size_pos
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hs, Nat.succ_mul]
  omega

private theorem le_getFee_mul (r : FeeRate) (v : ℕ) : r.fee * v ≤ r.getFee v * r.size :=
  (getFee_le_iff r v _).1 le_rfl

private theorem getFee_pos (r : FeeRate) (hr : 0 < r.fee) {v : ℕ} (hv : 0 < v) :
    1 ≤ r.getFee v := by
  by_contra h
  have h0 : r.getFee v ≤ 0 := by omega
  rw [getFee_le_iff, zero_mul] at h0
  have := Nat.mul_pos hr hv
  omega

private theorem getFee_zero (r : FeeRate) : r.getFee 0 = 0 := by
  have := (getFee_le_iff r 0 0).2 (by simp)
  omega

private theorem getFee_add_le (r : FeeRate) (a b : ℕ) :
    r.getFee (a + b) ≤ r.getFee a + r.getFee b := by
  rw [getFee_le_iff, mul_add, add_mul]
  exact Nat.add_le_add (le_getFee_mul r a) (le_getFee_mul r b)

private theorem getFee_mono (r : FeeRate) {a b : ℕ} (h : a ≤ b) : r.getFee a ≤ r.getFee b := by
  rw [getFee_le_iff]
  exact (Nat.mul_le_mul_left _ h).trans (le_getFee_mul r b)

private theorem getFee_sum_le (r : FeeRate) : ∀ l : List ℕ, r.getFee l.sum ≤ (l.map r.getFee).sum
  | [] => by simp [getFee_zero]
  | x :: l => by
    simp only [List.sum_cons, List.map_cons]
    exact (getFee_add_le r x l.sum).trans (Nat.add_le_add_left (getFee_sum_le r l) _)

private theorem length_mul_getFee_le (r : FeeRate) (m : ℕ) :
    ∀ l : List ℕ, (∀ x ∈ l, m ≤ x) → l.length * r.getFee m ≤ (l.map r.getFee).sum
  | [], _ => by simp
  | x :: l, h => by
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul]
    have h1 := getFee_mono r (h x (List.mem_cons_self ..))
    have h2 := length_mul_getFee_le r m l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

private theorem fee_le_totalFee {t : Tx} {s : Multiset Tx} (h : t ∈ s) : t.fee ≤ totalFee s :=
  Multiset.le_sum_of_mem (Multiset.mem_map_of_mem Tx.fee h)

private theorem totalFee_le_of_le {s u : Multiset Tx} (h : s ≤ u) : totalFee s ≤ totalFee u := by
  obtain ⟨w, rfl⟩ := Multiset.le_iff_exists_add.1 h
  simp [totalFee, Multiset.map_add, Multiset.sum_add]

private theorem totalFee_cons (t : Tx) (D : Multiset Tx) :
    totalFee (t ::ₘ D) = t.fee + totalFee D := by
  simp [totalFee, Multiset.map_cons, Multiset.sum_cons]

private theorem chain_bound (rate : FeeRate) :
    ∀ (Rs : List Replacement) (t₀ : Tx), IsChain rate t₀ Rs →
      t₀.fee + ((chainVsizes Rs).map rate.getFee).sum ≤ (chainEnd t₀ Rs).fee
  | [], t₀, _ => by simp [chainVsizes, chainEnd]
  | R :: Rs, t₀, ⟨hv, ht, hc⟩ => by
    have ih := chain_bound rate Rs R.new hc
    have h1 : t₀.fee + rate.getFee R.new.vsize ≤ R.new.fee := by
      have := fee_le_totalFee ht
      have := hv.2.1
      have := hv.2.2
      omega
    simp only [chainVsizes, List.map_cons, List.sum_cons, chainEnd, List.foldl_cons] at ih ⊢
    omega

private theorem chainVsizes_pos (Rs : List Replacement) : ∀ x ∈ chainVsizes Rs, 1 ≤ x := by
  intro x hx
  obtain ⟨R, -, rfl⟩ := List.mem_map.1 hx
  exact R.new.vsize_pos

private theorem feeRateQ_lt_iff' (a b : Tx) :
    a.feeRateQ < b.feeRateQ ↔ a.fee * b.vsize < b.fee * a.vsize := by
  unfold Tx.feeRateQ
  rw [div_lt_div_iff₀ (by exact_mod_cast a.vsize_pos) (by exact_mod_cast b.vsize_pos)]
  exact_mod_cast Iff.rfl

/-- The `ByRatio` comparison is the ordinary comparison of the exact fractions `fee / vsize`. -/
theorem solution (a b : BitcoinReplacement.Tx) :
    a.feeRateQ < b.feeRateQ ↔ BitcoinReplacement.FeeRate.lt a.feeRate b.feeRate :=
  feeRateQ_lt_iff' a b

-- Prove2me | solution 1 for BitcoinReplacement.bandwidth_paid_rate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:12:20.345175+00:00
-- url     : https://prove2.me/submissions/da11b2fd-209a-4223-964f-da29f5054dc6

import Definitions.Def_BitcoinReplacement
namespace S229BCR
open BitcoinReplacement

theorem getFee_le_iff (r : FeeRate) (v k : ℕ) : r.getFee v ≤ k ↔ r.fee * v ≤ k * r.size := by
  unfold FeeRate.getFee
  have hs := r.size_pos
  rw [Nat.div_le_iff_le_mul_add_pred hs]
  constructor <;> intro h <;> nlinarith [Nat.sub_add_cancel hs]

theorem mul_le_getFee (r : FeeRate) (v : ℕ) : r.fee * v ≤ r.getFee v * r.size :=
  (getFee_le_iff r v _).1 le_rfl

theorem getFee_add (r : FeeRate) (a b : ℕ) : r.getFee (a + b) ≤ r.getFee a + r.getFee b := by
  rw [getFee_le_iff]
  have := mul_le_getFee r a; have := mul_le_getFee r b
  nlinarith

theorem getFee_mono (r : FeeRate) {a b : ℕ} (h : a ≤ b) : r.getFee a ≤ r.getFee b := by
  rw [getFee_le_iff]
  have := mul_le_getFee r b
  have := Nat.mul_le_mul_left r.fee h
  omega

theorem getFee_pos (r : FeeRate) (hr : 0 < r.fee) {v : ℕ} (hv : 0 < v) : 0 < r.getFee v := by
  by_contra h
  have h0 : r.getFee v ≤ 0 := by omega
  rw [getFee_le_iff] at h0
  have := Nat.mul_pos hr hv
  omega

theorem le_totalFee {s : Multiset Tx} {t : Tx} (h : t ∈ s) : t.fee ≤ totalFee s :=
  Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ h)

theorem step {rate : FeeRate} {R : Replacement} (hR : Valid rate R) {t : Tx} (ht : t ∈ R.evicted) :
    t.fee + rate.getFee R.new.vsize ≤ R.new.fee := by
  have h1 := le_totalFee ht
  have h2 := hR.2
  unfold PaysForRBF at h2
  omega

theorem chainEnd_cons (t : Tx) (R : Replacement) (Rs : List Replacement) :
    chainEnd t (R :: Rs) = chainEnd R.new Rs := rfl

theorem chainVsizes_cons (R : Replacement) (Rs : List Replacement) :
    chainVsizes (R :: Rs) = R.new.vsize :: chainVsizes Rs := rfl

theorem chainEnd_nil (t : Tx) : chainEnd t [] = t := rfl

-- a12654c9
theorem T1 (rate : BitcoinReplacement.FeeRate)
    (R : BitcoinReplacement.Replacement) :
    BitcoinReplacement.PaysForRBF rate R ↔
      BitcoinReplacement.totalFee R.evicted + rate.getFee R.new.vsize ≤ R.new.fee := by
  unfold PaysForRBF; omega

-- 46513f82
theorem T2 (rate : BitcoinReplacement.FeeRate)
    (hr : 0 < rate.fee) (R : BitcoinReplacement.Replacement)
    (hR : BitcoinReplacement.Valid rate R) (t : BitcoinReplacement.Tx) (ht : t ∈ R.evicted) :
    t.fee < R.new.fee := by
  have := step hR ht
  have := getFee_pos rate hr R.new.vsize_pos
  omega

-- 9608526f
theorem T3 (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee + ((BitcoinReplacement.chainVsizes Rs).map rate.getFee).sum ≤
      (BitcoinReplacement.chainEnd t₀ Rs).fee := by
  induction Rs generalizing t₀ with
  | nil => simp [chainVsizes, chainEnd_nil]
  | cons R Rs ih =>
    obtain ⟨hv, hm, hc⟩ := h
    have := step hv hm
    have := ih R.new hc
    rw [chainVsizes_cons, chainEnd_cons, List.map_cons, List.sum_cons]
    omega

-- f1774841
theorem T4 (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee + rate.getFee (BitcoinReplacement.chainVsizes Rs).sum ≤
      (BitcoinReplacement.chainEnd t₀ Rs).fee := by
  induction Rs generalizing t₀ with
  | nil =>
    simp only [chainVsizes, List.map_nil, List.sum_nil, chainEnd_nil]
    have : rate.getFee 0 ≤ 0 := by rw [getFee_le_iff]; simp
    omega
  | cons R Rs ih =>
    obtain ⟨hv, hm, hc⟩ := h
    have := step hv hm
    have := ih R.new hc
    rw [chainVsizes_cons, chainEnd_cons, List.sum_cons]
    have := getFee_add rate R.new.vsize (chainVsizes Rs).sum
    omega

-- bfe2ea1d
theorem T5 (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee * rate.size + rate.fee * (BitcoinReplacement.chainVsizes Rs).sum ≤
      (BitcoinReplacement.chainEnd t₀ Rs).fee * rate.size := by
  induction Rs generalizing t₀ with
  | nil => simp [chainVsizes, chainEnd_nil]
  | cons R Rs ih =>
    obtain ⟨hv, hm, hc⟩ := h
    have h1 := step hv hm
    have h2 := ih R.new hc
    rw [chainVsizes_cons, chainEnd_cons, List.sum_cons]
    have h3 := mul_le_getFee rate R.new.vsize
    have h4 := Nat.mul_le_mul_right rate.size h1
    nlinarith

-- 280fdfbb
theorem T6 (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    (t₀.fee : ℚ) + ((rate.fee : ℚ) / rate.size) * (BitcoinReplacement.chainVsizes Rs).sum ≤
      ((BitcoinReplacement.chainEnd t₀ Rs).fee : ℚ) := by
  have h5 := T5 rate t₀ Rs h
  have hs : (0 : ℚ) < rate.size := by exact_mod_cast rate.size_pos
  have h6 : ((t₀.fee * rate.size + rate.fee * (chainVsizes Rs).sum : ℕ) : ℚ) ≤
      (((chainEnd t₀ Rs).fee * rate.size : ℕ) : ℚ) := by exact_mod_cast h5
  simp only [Nat.cast_add, Nat.cast_mul] at h6
  rw [← mul_le_mul_iff_of_pos_right hs]
  rw [add_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, div_self hs.ne']
  · nlinarith

-- a6a4cb85
theorem T7 (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) (m : ℕ) (hm : ∀ R ∈ Rs, m ≤ R.new.vsize) :
    t₀.fee + Rs.length * rate.getFee m ≤ (BitcoinReplacement.chainEnd t₀ Rs).fee := by
  induction Rs generalizing t₀ with
  | nil => simp [chainEnd_nil]
  | cons R Rs ih =>
    obtain ⟨hv, hm', hc⟩ := h
    have h1 := step hv hm'
    have h2 := ih R.new hc (fun R' hR' => hm R' (List.mem_cons_of_mem _ hR'))
    have h3 := getFee_mono rate (hm R List.mem_cons_self)
    rw [chainEnd_cons, List.length_cons]
    nlinarith

end S229BCR

theorem solution (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee * rate.size + rate.fee * (BitcoinReplacement.chainVsizes Rs).sum ≤
      (BitcoinReplacement.chainEnd t₀ Rs).fee * rate.size := by
  apply S229BCR.T5 <;> assumption


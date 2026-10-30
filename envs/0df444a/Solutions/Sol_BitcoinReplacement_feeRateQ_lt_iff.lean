-- Prove2me | solution 1 for BitcoinReplacement.feeRateQ_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:20:18.451734+00:00
-- url     : https://prove2.me/submissions/0957bbbb-8ee7-4084-b2c0-21e679f4e576

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


theorem totalFee_cons (t : Tx) (D : Multiset Tx) : totalFee (t ::ₘ D) = t.fee + totalFee D := by
  simp [totalFee]

theorem totalFee_mono {A B : Multiset Tx} (h : A ≤ B) : totalFee A ≤ totalFee B := by
  obtain ⟨E, rfl⟩ := le_iff_exists_add.1 h
  simp [totalFee]

-- d275c484
theorem U1 (rate : BitcoinReplacement.FeeRate)
    (hr : 0 < rate.fee) (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee + Rs.length ≤ (BitcoinReplacement.chainEnd t₀ Rs).fee := by
  induction Rs generalizing t₀ with
  | nil => simp [chainEnd_nil]
  | cons R Rs ih =>
    obtain ⟨hv, hm, hc⟩ := h
    have h1 := step hv hm
    have h2 := ih R.new hc
    have h3 := getFee_pos rate hr R.new.vsize_pos
    rw [chainEnd_cons, List.length_cons]
    omega

theorem U2aux (rate : FeeRate) (t₀ : Tx) (Rs : List Replacement) (h : IsChain rate t₀ Rs) :
    t₀.fee * rate.size + Rs.length * rate.fee ≤ (chainEnd t₀ Rs).fee * rate.size := by
  induction Rs generalizing t₀ with
  | nil => simp [chainEnd_nil]
  | cons R Rs ih =>
    obtain ⟨hv, hm, hc⟩ := h
    have h1 := step hv hm
    have h2 := ih R.new hc
    have h3 := mul_le_getFee rate R.new.vsize
    have h5 : rate.fee ≤ rate.fee * R.new.vsize := Nat.le_mul_of_pos_right _ R.new.vsize_pos
    have h4 := Nat.mul_le_mul_right rate.size h1
    rw [chainEnd_cons, List.length_cons]
    nlinarith

-- 7be85bc9
theorem U2 (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    Rs.length * rate.fee ≤ ((BitcoinReplacement.chainEnd t₀ Rs).fee - t₀.fee) * rate.size := by
  have := U2aux rate t₀ Rs h
  rw [Nat.sub_mul]
  omega

-- 789bd871
theorem U3 (rate : BitcoinReplacement.FeeRate)
    (t : BitcoinReplacement.Tx) (D : Multiset BitcoinReplacement.Tx)
    (R : BitcoinReplacement.Replacement) (hR : BitcoinReplacement.Valid rate R)
    (hD : t ::ₘ D ≤ R.evicted) :
    t.fee + BitcoinReplacement.totalFee D + rate.getFee R.new.vsize ≤ R.new.fee := by
  have h1 := totalFee_mono hD
  rw [totalFee_cons] at h1
  have h2 := hR.2
  unfold PaysForRBF at h2
  omega

-- 582d2c2b
theorem U4 (rate : BitcoinReplacement.FeeRate)
    (t : BitcoinReplacement.Tx) (D : Multiset BitcoinReplacement.Tx)
    (R : BitcoinReplacement.Replacement) (hE : R.evicted = t ::ₘ D) :
    BitcoinReplacement.PaysForRBF rate R ↔
      t.fee + BitcoinReplacement.totalFee D + rate.getFee R.new.vsize ≤ R.new.fee := by
  unfold PaysForRBF
  rw [hE, totalFee_cons]
  omega

-- 97711924
theorem U5 (a b : BitcoinReplacement.Tx) :
    a.feeRateQ < b.feeRateQ ↔ BitcoinReplacement.FeeRate.lt a.feeRate b.feeRate := by
  unfold Tx.feeRateQ FeeRate.lt Tx.feeRate
  have ha : (0 : ℚ) < a.vsize := by exact_mod_cast a.vsize_pos
  have hb : (0 : ℚ) < b.vsize := by exact_mod_cast b.vsize_pos
  rw [div_lt_div_iff₀ ha hb]
  dsimp only
  constructor <;> intro h
  · exact_mod_cast h
  · exact_mod_cast h

-- 69f89b44
theorem U6 (rate : BitcoinReplacement.FeeRate)
    (R : BitcoinReplacement.Replacement) (hR : BitcoinReplacement.Valid rate R)
    (t : BitcoinReplacement.Tx) (ht : t ∈ R.direct) :
    t.fee * R.new.vsize < R.new.fee * t.vsize := hR.1 t ht

-- d0dd2b6d
theorem U7 (rate : BitcoinReplacement.FeeRate)
    (R : BitcoinReplacement.Replacement) (hR : BitcoinReplacement.Valid rate R)
    (hne : R.direct ≠ 0) :
    ∃ t ∈ R.direct, (∀ s ∈ R.direct, t.feeRateQ ≤ s.feeRateQ) ∧
      t.feeRateQ < R.new.feeRateQ := by
  have hn : R.direct.toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty]; exact hne
  obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image _ Tx.feeRateQ hn
  rw [Multiset.mem_toFinset] at ht
  refine ⟨t, ht, fun s hs => hmin s (Multiset.mem_toFinset.2 hs), ?_⟩
  exact (U5 t R.new).2 (hR.1 t ht)

end S229BCR

theorem solution (a b : BitcoinReplacement.Tx) :
    a.feeRateQ < b.feeRateQ ↔ BitcoinReplacement.FeeRate.lt a.feeRate b.feeRate := by
  apply S229BCR.U5 <;> assumption


-- Prove2me | solution 1 for BitcoinReplacement.replacement_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:55:26.130891+00:00
-- url     : https://prove2.me/submissions/e6b117ee-ddf5-4757-9c5d-ad141ca7075c

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

end S229BCR

open BitcoinReplacement in
theorem solution (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee + Rs.length * rate.getFee 1 ≤ (BitcoinReplacement.chainEnd t₀ Rs).fee := by
  induction Rs generalizing t₀ with
  | nil => simp [S229BCR.chainEnd_nil]
  | cons R Rs ih =>
    obtain ⟨hv, hm, hc⟩ := h
    have h1 := S229BCR.step hv hm
    have h2 := ih R.new hc
    have h3 := S229BCR.getFee_mono rate R.new.vsize_pos
    rw [S229BCR.chainEnd_cons, List.length_cons]
    nlinarith

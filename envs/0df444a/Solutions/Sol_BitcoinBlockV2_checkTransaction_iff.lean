-- Prove2me | solution 1 for BitcoinBlockV2.checkTransaction_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:12:27.258019+00:00
-- url     : https://prove2.me/submissions/285bbe17-f5e2-45ad-b478-a06d16a4e518

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

open BitcoinBlockV2 in
theorem S190BLK_sum_nonneg (l : List BitcoinSer.TxOut) (h : ∀ o ∈ l, 0 ≤ o.nValue) : 0 ≤ sumValues l := by
  induction l with
  | nil => simp [sumValues]
  | cons o rest ih =>
    simp only [sumValues]
    have := h o (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    omega

open BitcoinBlockV2 in
theorem S190BLK_ol (l : List BitcoinSer.TxOut) (acc : Int) (h0 : 0 ≤ acc) (h1 : acc ≤ MAX_MONEY) :
    (outputsLoop l acc).isSome = true ↔
      (∀ o ∈ l, 0 ≤ o.nValue ∧ o.nValue ≤ MAX_MONEY) ∧ acc + sumValues l ≤ MAX_MONEY := by
  induction l generalizing acc with
  | nil => simp [outputsLoop, sumValues, h1]
  | cons o rest ih =>
    simp only [outputsLoop, sumValues]
    by_cases a : o.nValue < 0
    · simp [a]; intro h; omega
    · by_cases b : MAX_MONEY < o.nValue
      · simp [a, b]; intro _ h; omega
      · by_cases c : moneyRange (acc + o.nValue) = true
        · have hc : 0 ≤ acc + o.nValue ∧ acc + o.nValue ≤ MAX_MONEY := by
            simpa [moneyRange] using c
          simp only [a, b, c, if_false, Bool.not_true]
          simp only [Bool.false_eq_true, if_false]
          rw [ih _ hc.1 hc.2]
          simp only [List.mem_cons, forall_eq_or_imp]
          constructor
          · rintro ⟨h2, h3⟩; exact ⟨⟨⟨by omega, by omega⟩, h2⟩, by omega⟩
          · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h2, by omega⟩
        · simp only [a, b, c, if_false, Bool.not_false, if_true]
          simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
          intro h2
          have := S190BLK_sum_nonneg rest (fun x hx => (h2 x (by simp [hx])).1)
          have hc : ¬ (0 ≤ acc + o.nValue ∧ acc + o.nValue ≤ MAX_MONEY) := by
            intro hc; apply c; simp [moneyRange, hc]
          omega

open BitcoinBlockV2 in
theorem S190BLK_cb (tx : BitcoinSer.Tx) (h : isCoinBase tx = true) : ∃ i, tx.vin = [i] := by
  unfold isCoinBase at h
  split at h
  · exact ⟨_, by assumption⟩
  · cases h

open BitcoinBlockV2 in
theorem S190BLK_ct_iff (tx : BitcoinSer.Tx) :
    BitcoinBlockV2.checkTransaction tx = true ↔ BitcoinBlockV2.TxSpec tx := by
  unfold checkTransaction TxSpec
  have hol := S190BLK_ol tx.vout 0 (by decide) (by decide)
  simp only [Int.zero_add] at hol
  have hcb : ((if isCoinBase tx then
     decide (2 ≤ (tx.vin.headD ⟨⟨[], 0⟩, [], 0, []⟩).scriptSig.length ∧
             (tx.vin.headD ⟨⟨[], 0⟩, [], 0, []⟩).scriptSig.length ≤ 100)
   else tx.vin.all fun i => !outPointNull i.prevout) = true) ↔
    ((isCoinBase tx = true → ∀ i ∈ tx.vin, 2 ≤ i.scriptSig.length ∧ i.scriptSig.length ≤ 100) ∧
     (isCoinBase tx = false → ∀ i ∈ tx.vin, outPointNull i.prevout = false)) := by
    cases hc : isCoinBase tx
    · simp
    · obtain ⟨i, hi⟩ := S190BLK_cb tx hc
      simp [hi]
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, decide_eq_true_eq, hcb, hol, valueOut]
  constructor
  · rintro ⟨⟨⟨⟨⟨a, b⟩, c⟩, d, e⟩, f⟩, g⟩
    exact ⟨a, b, c, d, e, f, g⟩
  · rintro ⟨a, b, c, d, e, f, g⟩
    exact ⟨⟨⟨⟨⟨a, b⟩, c⟩, d, e⟩, f⟩, g⟩

open BitcoinBlockV2 in
theorem solution (tx : BitcoinSer.Tx) :
    BitcoinBlockV2.checkTransaction tx = true ↔ BitcoinBlockV2.TxSpec tx := S190BLK_ct_iff tx

-- Prove2me | solution 1 for BitcoinBlockV2.checkTxInputs_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:13:01.158474+00:00
-- url     : https://prove2.me/submissions/eab9a184-2f19-4cc0-a834-a9b8ddc9104d

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

open BitcoinBlockV2 in
def S190BLK_InOk (u : Ledger) (H : Nat) (i : BitcoinSer.TxIn) : Prop :=
  ∃ c, getCoin u i.prevout = some c ∧
    (c.isCoinbase = true → c.height + COINBASE_MATURITY ≤ H) ∧ 0 ≤ c.out.nValue ∧ c.out.nValue ≤ MAX_MONEY

open BitcoinBlockV2 in
theorem S190BLK_vin_nonneg (u : Ledger) (H : Nat) (l : List BitcoinSer.TxIn)
    (h : ∀ i ∈ l, S190BLK_InOk u H i) : 0 ≤ valueIn u l := by
  induction l with
  | nil => simp [valueIn]
  | cons i rest ih =>
    simp only [valueIn]
    obtain ⟨c, hc, -, h0, -⟩ := h i (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    simp only [accessCoin, hc, Option.getD_some]
    omega

open BitcoinBlockV2 in
theorem S190BLK_il (u : Ledger) (H : Nat) (l : List BitcoinSer.TxIn) (acc : Int)
    (h0 : 0 ≤ acc) (h1 : acc ≤ MAX_MONEY) :
    ((inputsLoop u H l acc).isSome = true ↔
      (∀ i ∈ l, S190BLK_InOk u H i) ∧ acc + valueIn u l ≤ MAX_MONEY) ∧
    (∀ r, inputsLoop u H l acc = some r → r = acc + valueIn u l) := by
  induction l generalizing acc with
  | nil => simp [inputsLoop, valueIn, h1]
  | cons i rest ih =>
    simp only [inputsLoop, valueIn, List.mem_cons, forall_eq_or_imp]
    cases hg : getCoin u i.prevout with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff, reduceCtorEq, false_implies,
        implies_true, and_true]
      rintro ⟨⟨⟨c, hc, -⟩, -⟩, -⟩
      rw [hg] at hc; cases hc
    | some c =>
      simp only [accessCoin, hg, Option.getD_some]
      by_cases hm : (c.isCoinbase && decide (H - c.height < COINBASE_MATURITY)) = true
      · simp only [hm, if_true, Option.isSome_none, Bool.false_eq_true, false_iff, reduceCtorEq,
          false_implies, implies_true, and_true]
        rintro ⟨⟨⟨c', hc', hmat, -⟩, -⟩, -⟩
        rw [hg] at hc'; cases hc'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
        have := hmat hm.1
        unfold COINBASE_MATURITY at *
        omega
      · have hmat : c.isCoinbase = true → c.height + COINBASE_MATURITY ≤ H := by
          intro hc
          simp only [hc, Bool.true_and, decide_eq_true_eq] at hm
          unfold COINBASE_MATURITY at *
          omega
        simp only [hm, Bool.false_eq_true, if_false]
        by_cases hr : (!moneyRange c.out.nValue || !moneyRange (acc + c.out.nValue)) = true
        · simp only [hr, if_true, Option.isSome_none, Bool.false_eq_true, false_iff, reduceCtorEq,
            false_implies, implies_true, and_true]
          rintro ⟨⟨⟨c', hc', -, hv0, hv1⟩, hrest⟩, hs⟩
          rw [hg] at hc'; cases hc'
          have := S190BLK_vin_nonneg u H rest hrest
          simp [moneyRange] at hr
          omega
        · simp only [hr, Bool.false_eq_true, if_false]
          simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false, moneyRange,
            decide_eq_true_eq] at hr
          obtain ⟨⟨hv0, hv1⟩, ha0, ha1⟩ := hr
          obtain ⟨ih1, ih2⟩ := ih (acc + c.out.nValue) ha0 ha1
          refine ⟨?_, ?_⟩
          · rw [ih1]
            constructor
            · rintro ⟨hr, hs⟩; exact ⟨⟨⟨c, hg, hmat, hv0, hv1⟩, hr⟩, by omega⟩
            · rintro ⟨⟨_, hr⟩, hs⟩; exact ⟨hr, by omega⟩
          · intro r hr; rw [ih2 r hr]; omega

open BitcoinBlockV2 in
theorem solution (u : Ledger) (tx : BitcoinSer.Tx) (H : Nat) :
    ((∃ fee, BitcoinBlockV2.checkTxInputs u tx H = some fee) ↔
      (∀ i ∈ tx.vin, ∃ c, BitcoinBlockV2.getCoin u i.prevout = some c ∧
        (c.isCoinbase = true → c.height + COINBASE_MATURITY ≤ H) ∧ 0 ≤ c.out.nValue ∧ c.out.nValue ≤ MAX_MONEY) ∧
      BitcoinBlockV2.valueIn u tx.vin ≤ MAX_MONEY ∧ BitcoinBlockV2.valueOut tx ≤ BitcoinBlockV2.valueIn u tx.vin ∧
      BitcoinBlockV2.valueIn u tx.vin - BitcoinBlockV2.valueOut tx ≤ MAX_MONEY) ∧
    (∀ fee, BitcoinBlockV2.checkTxInputs u tx H = some fee → fee = BitcoinBlockV2.feeOf u tx) := by
  obtain ⟨hl1, hl2⟩ := S190BLK_il u H tx.vin 0 (by decide) (by decide)
  simp only [Int.zero_add] at hl1 hl2
  have hall : (tx.vin.all fun i => haveCoin u i.prevout) = true ↔ ∀ i ∈ tx.vin, ∃ c, getCoin u i.prevout = some c := by
    simp [haveCoin, Option.isSome_iff_exists]
  unfold checkTxInputs feeOf
  by_cases ha : (tx.vin.all fun i => haveCoin u i.prevout) = true
  · simp only [ha, Bool.not_true, Bool.false_eq_true, if_false]
    cases hi : inputsLoop u H tx.vin 0 with
    | none =>
      rw [hi] at hl1
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff] at hl1
      simp only [reduceCtorEq, exists_false, false_iff, false_implies, implies_true, and_true]
      rintro ⟨hh, h2, -⟩
      exact hl1 ⟨hh, h2⟩
    | some vi =>
      rw [hi] at hl1
      have hv := hl2 vi hi
      subst hv
      simp only [Option.isSome_some, true_iff] at hl1
      obtain ⟨hok, hle⟩ := hl1
      have hnn := S190BLK_vin_nonneg u H tx.vin hok
      by_cases c1 : valueIn u tx.vin < valueOut tx
      · simp only [c1, if_true, reduceCtorEq, exists_false, false_iff, false_implies, implies_true, and_true]
        rintro ⟨-, -, h3, -⟩; omega
      · by_cases c2 : moneyRange (valueIn u tx.vin - valueOut tx) = true
        · simp only [c1, c2, if_false, Bool.not_true, Bool.false_eq_true]
          simp only [moneyRange, decide_eq_true_eq] at c2
          refine ⟨⟨fun _ => ⟨hok, hle, by omega, c2.2⟩, fun _ => ⟨_, rfl⟩⟩, ?_⟩
          intro fee hf; cases hf; rfl
        · simp only [c1, c2, if_false, Bool.not_false, if_true, reduceCtorEq, exists_false, false_iff,
            false_implies, implies_true, and_true]
          simp only [moneyRange, decide_eq_true_eq] at c2
          rintro ⟨-, -, h3, h4⟩; omega
  · simp only [ha, Bool.not_false, if_true, reduceCtorEq, exists_false, false_iff, false_implies,
      implies_true, and_true]
    rintro ⟨hh, -⟩
    exact ha (hall.mpr (fun i hi => let ⟨c, hc, _⟩ := hh i hi; ⟨c, hc⟩))

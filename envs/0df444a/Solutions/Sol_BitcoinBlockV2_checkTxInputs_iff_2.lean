-- Prove2me | solution 2 for BitcoinBlockV2.checkTxInputs_iff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-28T15:22:01.570636+00:00
-- url     : https://prove2.me/submissions/14c5760f-69ea-4c43-a477-e0e800716fca

import Definitions.Def_BitcoinBlockV2
import Theorems.Thm_BitcoinPow_checkProofOfWork_iff
import Theorems.Thm_BitcoinHeader_versionOutdated_iff
import Theorems.Thm_BitcoinSubsidy_core_eq_spec
import Theorems.Thm_BitcoinBIP68_fold_acceptance
import Theorems.Thm_BitcoinBIP68_decode_sequence
import Theorems.Thm_BitcoinBlockV2_futureTime_iff

open BitcoinBlockV2

/-- The initial state is well formed. -/
private theorem initial_wellFormed : BitcoinBlockV2.WellFormed BitcoinBlockV2.initialState := by
  refine ⟨rfl, List.nodup_nil, ?_⟩
  intro e he; cases he

/-- `AcceptBlockHeader` on top of the tip accepts exactly when the proof of work holds, the parent is
the tip, and the Header mission's `ContextualCheckBlockHeader` holds with the chain's median time past
and required work. -/
private theorem acceptHeader_eq_iff (S : ChainState) (h : BitcoinSer.Header) (now : Int) :
    BitcoinBlockV2.acceptHeader S h now = .accept S [] ↔
      BitcoinBlockV2.checkHeaderPow h = true ∧ h.prevBlock = S.tipHash ∧
      BitVec.ofNat 32 h.bits = S.requiredBits ∧ ¬ ((h.time : Int) ≤ S.mtp) ∧
      ¬ (now + MAX_FUTURE_BLOCK_TIME < (h.time : Int)) ∧
      BitcoinHeader.versionOutdated h.version S.tipHeight = false := by
  unfold acceptHeader
  simp only [Bool.not_eq_true']
  by_cases h1 : checkHeaderPow h = false <;> by_cases h2 : h.prevBlock = S.tipHash <;>
    by_cases h3 : BitVec.ofNat 32 h.bits = S.requiredBits <;> by_cases h4 : (h.time : Int) ≤ S.mtp <;>
    by_cases h5 : now + MAX_FUTURE_BLOCK_TIME < (h.time : Int) <;>
    by_cases h6 : BitcoinHeader.versionOutdated h.version S.tipHeight = true <;>
    simp only [h1, h2, h3, h4, h5, h6, ite_true, ite_false, ne_eq, not_true_eq_false, not_false_eq_true] <;>
    simp_all

private theorem futureTime_iff' (S : ChainState) (b : BitcoinSer.Block) (now : Int) :
    BitcoinBlockV2.validate S b now = .futureTime ↔
      BitcoinBlockV2.checkHeaderPow b.header = true ∧ b.header.prevBlock = S.tipHash ∧
      BitVec.ofNat 32 b.header.bits = S.requiredBits ∧ ¬ ((b.header.time : Int) ≤ S.mtp) ∧
      now + MAX_FUTURE_BLOCK_TIME < (b.header.time : Int) := by
  unfold validate acceptHeader
  simp only [Bool.not_eq_true']
  by_cases h1 : checkHeaderPow b.header = false <;> by_cases h2 : b.header.prevBlock = S.tipHash <;>
    by_cases h3 : BitVec.ofNat 32 b.header.bits = S.requiredBits <;> by_cases h4 : (b.header.time : Int) ≤ S.mtp <;>
    by_cases h5 : now + MAX_FUTURE_BLOCK_TIME < (b.header.time : Int) <;>
    by_cases h6 : BitcoinHeader.versionOutdated b.header.version S.tipHeight = true <;>
    simp only [h1, h2, h3, h4, h5, h6, ite_true, ite_false, ne_eq, not_true_eq_false, not_false_eq_true] <;>
    (try simp_all)
  all_goals (split <;> (try split) <;> (try split) <;> simp_all)

private theorem acceptHeader_clock (S : ChainState) (h : BitcoinSer.Header) (now now' : Int)
    (h1 : ¬ now + MAX_FUTURE_BLOCK_TIME < (h.time : Int)) (h2 : ¬ now' + MAX_FUTURE_BLOCK_TIME < (h.time : Int)) :
    BitcoinBlockV2.acceptHeader S h now' = BitcoinBlockV2.acceptHeader S h now := by
  unfold acceptHeader
  simp only [h1, h2, ite_false]

private theorem acceptHeader_clock' (S : ChainState) (h : BitcoinSer.Header) (now now' : Int) (hle : now ≤ now') :
    BitcoinBlockV2.acceptHeader S h now = .futureTime ∨
    BitcoinBlockV2.acceptHeader S h now' = BitcoinBlockV2.acceptHeader S h now := by
  by_cases hf : now + MAX_FUTURE_BLOCK_TIME < (h.time : Int)
  · unfold acceptHeader
    simp only [Bool.not_eq_true']
    by_cases h1 : checkHeaderPow h = false <;> by_cases h2 : h.prevBlock = S.tipHash <;>
      by_cases h3 : BitVec.ofNat 32 h.bits = S.requiredBits <;> by_cases h4 : (h.time : Int) ≤ S.mtp <;>
      simp only [h1, h2, h3, h4, hf, ite_true, ite_false, ne_eq, not_true_eq_false, not_false_eq_true] <;>
      simp_all
  · exact Or.inr (acceptHeader_clock S h now now' hf (by omega))

private theorem sumValues_nonneg : ∀ (os : List BitcoinSer.TxOut), (∀ o ∈ os, 0 ≤ o.nValue ∧ o.nValue ≤ MAX_MONEY) →
    0 ≤ BitcoinBlockV2.sumValues os
  | [], _ => by simp [sumValues]
  | o :: rest, h => by
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp only [sumValues]; have := sumValues_nonneg rest h.2; omega

private theorem outputsLoop_iff : ∀ (os : List BitcoinSer.TxOut) (acc : Int), 0 ≤ acc → acc ≤ MAX_MONEY →
    ((BitcoinBlockV2.outputsLoop os acc).isSome = true ↔
      (∀ o ∈ os, 0 ≤ o.nValue ∧ o.nValue ≤ MAX_MONEY) ∧ acc + BitcoinBlockV2.sumValues os ≤ MAX_MONEY)
  | [], acc, _, h2 => by simp [outputsLoop, sumValues, h2]
  | o :: rest, acc, h1, h2 => by
    simp only [outputsLoop, sumValues, List.mem_cons, forall_eq_or_imp]
    by_cases hn : o.nValue < 0
    · simp only [hn, ite_true, Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
      intro h; omega
    · simp only [hn, ite_false]
      by_cases hm : MAX_MONEY < o.nValue
      · simp only [hm, ite_true, Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
        intro h; omega
      · simp only [hm, ite_false]
        by_cases hr : moneyRange (acc + o.nValue) = true
        · simp only [hr, Bool.not_true, Bool.false_eq_true, ite_false]
          unfold moneyRange at hr; simp only [decide_eq_true_eq] at hr
          rw [outputsLoop_iff rest (acc + o.nValue) hr.1 hr.2]
          constructor
          · rintro ⟨ha, hb⟩; exact ⟨⟨⟨by omega, by omega⟩, ha⟩, by omega⟩
          · rintro ⟨⟨_, ha⟩, hb⟩; exact ⟨ha, by omega⟩
        · simp only [Bool.not_eq_true] at hr
          simp only [hr, Bool.not_false, ite_true, Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
          unfold moneyRange at hr; simp only [decide_eq_false_iff_not] at hr
          rintro ⟨_, hrest⟩ hs
          have := sumValues_nonneg rest hrest
          omega

private theorem valueIn_nonneg (u : Ledger) : ∀ (ins : List BitcoinSer.TxIn),
    (∀ i ∈ ins, ∃ c, BitcoinBlockV2.getCoin u i.prevout = some c ∧ 0 ≤ c.out.nValue) → 0 ≤ BitcoinBlockV2.valueIn u ins
  | [], _ => by simp [valueIn]
  | i :: rest, h => by
    simp only [List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨c, hc, h0⟩ := h.1
    simp only [valueIn, accessCoin, hc, Option.getD_some]
    have := valueIn_nonneg u rest h.2; omega

private theorem inputsLoop_iff (u : Ledger) (H : Nat) : ∀ (ins : List BitcoinSer.TxIn) (acc : Int),
    0 ≤ acc → acc ≤ MAX_MONEY →
    ((∃ v, BitcoinBlockV2.inputsLoop u H ins acc = some v) ↔
      (∀ i ∈ ins, ∃ c, BitcoinBlockV2.getCoin u i.prevout = some c ∧
        (c.isCoinbase = true → c.height + COINBASE_MATURITY ≤ H) ∧ 0 ≤ c.out.nValue ∧ c.out.nValue ≤ MAX_MONEY) ∧
      acc + BitcoinBlockV2.valueIn u ins ≤ MAX_MONEY)
  | [], acc, _, h2 => by simp [inputsLoop, valueIn, h2]
  | i :: rest, acc, h1, h2 => by
    simp only [inputsLoop]
    cases hc : getCoin u i.prevout with
    | none =>
      dsimp only
      simp only [reduceCtorEq, exists_false, false_iff, not_and]
      intro h; obtain ⟨c, hc', _⟩ := h i (by simp); rw [hc] at hc'; cases hc'
    | some coin =>
      dsimp only
      have hvi : valueIn u (i :: rest) = coin.out.nValue + valueIn u rest := by simp [valueIn, accessCoin, hc]
      rw [hvi]
      by_cases hm : coin.isCoinbase = true ∧ H - coin.height < COINBASE_MATURITY
      · have e : (coin.isCoinbase && decide (H - coin.height < COINBASE_MATURITY)) = true := by simp [hm.1, hm.2]
        rw [if_pos e]
        simp only [reduceCtorEq, exists_false, false_iff, not_and]
        intro h; obtain ⟨c, hc', hmat, _⟩ := h i (by simp); rw [hc] at hc'; cases hc'
        have := hmat hm.1; omega
      · have e : (coin.isCoinbase && decide (H - coin.height < COINBASE_MATURITY)) = false := by
          cases hcb : coin.isCoinbase
          · rfl
          · simp only [Bool.true_and, decide_eq_false_iff_not]; intro h; exact hm ⟨hcb, h⟩
        rw [e]; simp only [Bool.false_eq_true, ite_false]
        by_cases hr : (!moneyRange coin.out.nValue || !moneyRange (acc + coin.out.nValue)) = true
        · rw [if_pos hr]; simp only [reduceCtorEq, exists_false, false_iff, not_and]
          simp only [Bool.or_eq_true, Bool.not_eq_true', moneyRange, decide_eq_false_iff_not] at hr
          intro h hs
          obtain ⟨c, hc', _, hc0, hcM⟩ := h i (by simp); rw [hc] at hc'; cases hc'
          have hrest : 0 ≤ valueIn u rest := valueIn_nonneg u rest (fun j hj => by
            obtain ⟨c, hc, _, h0, _⟩ := h j (by simp [hj]); exact ⟨c, hc, h0⟩)
          omega
        · rw [if_neg hr]
          simp only [Bool.or_eq_true, Bool.not_eq_true', moneyRange, decide_eq_false_iff_not, not_or,
            Decidable.not_not] at hr
          rw [inputsLoop_iff u H rest (acc + coin.out.nValue) (by omega) (by omega)]
          constructor
          · rintro ⟨ha, hb⟩
            refine ⟨?_, by omega⟩
            intro j hj
            simp only [List.mem_cons] at hj
            rcases hj with rfl | hj
            · refine ⟨coin, hc, fun hcb => ?_, by omega, by omega⟩
              have hnot : ¬ (H - coin.height < COINBASE_MATURITY) := fun h => hm ⟨hcb, h⟩
              unfold COINBASE_MATURITY at hnot ⊢
              omega
            · exact ha j hj
          · rintro ⟨ha, hb⟩
            exact ⟨fun j hj => ha j (by simp [hj]), by omega⟩

private theorem inputsLoop_value (u : Ledger) (H : Nat) : ∀ (ins : List BitcoinSer.TxIn) (acc v : Int),
    BitcoinBlockV2.inputsLoop u H ins acc = some v → v = acc + BitcoinBlockV2.valueIn u ins
  | [], acc, v, h => by simp only [inputsLoop, Option.some.injEq] at h; simp [valueIn]; omega
  | i :: rest, acc, v, h => by
    simp only [inputsLoop] at h
    cases hc : getCoin u i.prevout with
    | none => rw [hc] at h; cases h
    | some coin =>
      rw [hc] at h
      dsimp only at h
      have hvi : valueIn u (i :: rest) = coin.out.nValue + valueIn u rest := by simp [valueIn, accessCoin, hc]
      rw [hvi]
      by_cases e : (coin.isCoinbase && decide (H - coin.height < COINBASE_MATURITY)) = true
      · rw [if_pos e] at h; cases h
      · rw [if_neg e] at h
        by_cases hr : (!moneyRange coin.out.nValue || !moneyRange (acc + coin.out.nValue)) = true
        · rw [if_pos hr] at h; cases h
        · rw [if_neg hr] at h; have := inputsLoop_value u H rest _ v h; omega

/-- `CheckTxInputs` succeeds exactly when every input spends an existing coin of valid value that is
mature if a coinbase, the input total is in range and covers the outputs, and the fee is in range;
its value is the fee. -/
theorem solution (u : Ledger) (tx : BitcoinSer.Tx) (H : Nat) :
    ((∃ fee, BitcoinBlockV2.checkTxInputs u tx H = some fee) ↔
      (∀ i ∈ tx.vin, ∃ c, BitcoinBlockV2.getCoin u i.prevout = some c ∧
        (c.isCoinbase = true → c.height + COINBASE_MATURITY ≤ H) ∧ 0 ≤ c.out.nValue ∧ c.out.nValue ≤ MAX_MONEY) ∧
      BitcoinBlockV2.valueIn u tx.vin ≤ MAX_MONEY ∧ BitcoinBlockV2.valueOut tx ≤ BitcoinBlockV2.valueIn u tx.vin ∧
      BitcoinBlockV2.valueIn u tx.vin - BitcoinBlockV2.valueOut tx ≤ MAX_MONEY) ∧
    (∀ fee, BitcoinBlockV2.checkTxInputs u tx H = some fee → fee = BitcoinBlockV2.feeOf u tx) := by
  unfold checkTxInputs
  constructor
  · by_cases hall : (tx.vin.all fun i => haveCoin u i.prevout) = true
    · rw [hall]; simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      cases hl : inputsLoop u H tx.vin 0 with
      | none =>
        dsimp only
        simp only [reduceCtorEq, exists_false, false_iff, not_and]
        intro ha hv
        have := (inputsLoop_iff u H tx.vin 0 (Int.le_refl 0) (by decide)).2 ⟨ha, by simpa using hv⟩
        rw [hl] at this; obtain ⟨_, h⟩ := this; cases h
      | some v =>
        dsimp only
        have hv := inputsLoop_value u H tx.vin 0 v hl
        simp only [Int.zero_add] at hv; subst hv
        have hi := (inputsLoop_iff u H tx.vin 0 (Int.le_refl 0) (by decide)).1 ⟨_, hl⟩
        simp only [Int.zero_add] at hi
        constructor
        · rintro ⟨fee, hf⟩
          by_cases hlt : valueIn u tx.vin < valueOut tx
          · rw [if_pos hlt] at hf; cases hf
          · rw [if_neg hlt] at hf
            by_cases hr : moneyRange (valueIn u tx.vin - valueOut tx) = true
            · unfold moneyRange at hr; simp only [decide_eq_true_eq] at hr
              exact ⟨hi.1, hi.2, by omega, hr.2⟩
            · rw [if_pos (by simpa using hr)] at hf; cases hf
        · rintro ⟨_, _, hc, hd⟩
          have hr : moneyRange (valueIn u tx.vin - valueOut tx) = true := by
            unfold moneyRange; simp only [decide_eq_true_eq]; exact ⟨by omega, hd⟩
          rw [if_neg (by omega), if_neg (by simp [hr])]
          exact ⟨_, rfl⟩
    · simp only [Bool.not_eq_true] at hall
      rw [hall]; simp only [Bool.not_false, ite_true, reduceCtorEq, exists_false, false_iff, not_and]
      intro ha
      exfalso
      simp only [List.all_eq_false, haveCoin, Bool.not_eq_true, Option.isSome_eq_false_iff,
        Option.isNone_iff_eq_none] at hall
      obtain ⟨i, hi, hn⟩ := hall
      obtain ⟨c, hc, _⟩ := ha i hi
      rw [hc] at hn; cases hn
  · intro fee h
    by_cases hall : (tx.vin.all fun i => haveCoin u i.prevout) = true
    · rw [hall] at h; simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
      cases hl : inputsLoop u H tx.vin 0 with
      | none => rw [hl] at h; cases h
      | some v =>
        rw [hl] at h
        dsimp only at h
        by_cases hlt : v < valueOut tx
        · rw [if_pos hlt] at h; cases h
        · rw [if_neg hlt] at h
          by_cases hr : (!moneyRange (v - valueOut tx)) = true
          · rw [if_pos hr] at h; cases h
          · rw [if_neg hr] at h
            simp only [Option.some.injEq] at h
            subst h
            have := inputsLoop_value u H tx.vin 0 v hl
            unfold feeOf; omega
    · simp only [Bool.not_eq_true] at hall
      rw [hall] at h; simp at h

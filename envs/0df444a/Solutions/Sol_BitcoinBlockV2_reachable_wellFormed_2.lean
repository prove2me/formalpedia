-- Prove2me | solution 2 for BitcoinBlockV2.reachable_wellFormed
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-28T15:26:56.764813+00:00
-- url     : https://prove2.me/submissions/1265edbd-1342-404f-8f4d-b0e2bc65f60c

import Definitions.Def_BitcoinBlockV2
import Theorems.Thm_BitcoinPow_checkProofOfWork_iff
import Theorems.Thm_BitcoinHeader_versionOutdated_iff
import Theorems.Thm_BitcoinSubsidy_core_eq_spec
import Theorems.Thm_BitcoinBIP68_fold_acceptance
import Theorems.Thm_BitcoinBIP68_decode_sequence
import Theorems.Thm_BitcoinBlockV2_apply_spec
import Theorems.Thm_BitcoinBlockV2_checkTxInputs_iff
import Theorems.Thm_BitcoinBlockV2_connectLoop_iff
import Theorems.Thm_BitcoinBlockV2_futureTime_iff
import Theorems.Thm_BitcoinBlockV2_sequenceLocks_iff

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

private theorem coreEnabled_iff (v f : BitVec 32) :
    BitcoinBIP68.coreEnabled v f = true ↔ BitcoinBIP68.specEnabled v f := by
  unfold BitcoinBIP68.coreEnabled BitcoinBIP68.specEnabled
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  have : (f &&& 1 = 0) ↔ f.toNat % 2 = 0 := by
    rw [BitVec.toNat_eq, BitVec.toNat_and]
    simp [Nat.and_one_is_mod]
  constructor
  · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩
    have := (not_congr this).1 h2; omega
  · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩
    rw [this]; omega

private theorem inputScriptsOk_iff (f : BitcoinActivation.ScriptFlags) (u : Ledger) (tx : BitcoinSer.Tx) :
    BitcoinBlockV2.inputScriptsOk f u tx = true ↔
      ∀ n, n < tx.vin.length →
        let i := tx.vin.getD n ⟨⟨[], 0⟩, [], 0, []⟩
        let coin := BitcoinBlockV2.accessCoin u i.prevout
        BitcoinTaproot.verifyScriptFull (tx.vin.map fun j => (BitcoinBlockV2.accessCoin u j.prevout).out)
          ⟨f, tx, n, coin.out.nValue⟩ i.scriptSig coin.out.scriptPubKey i.witness = true := by
  unfold inputScriptsOk
  simp only [List.all_eq_true, List.mem_range]

private theorem connectLoop_iff' (f : BitcoinActivation.ScriptFlags) (H : Nat) (mtp : Nat → Nat) (ltf : Nat) :
    ∀ (txs : List BitcoinSer.Tx) (u : Ledger) (fees : Int) (sigOps : Nat) (undo : BlockUndo),
      (∀ tx ∈ txs, 0 ≤ BitcoinBlockV2.valueOut tx) → 0 ≤ fees →
      ((∃ st, BitcoinBlockV2.connectLoop f H mtp ltf ⟨u, fees, sigOps, undo⟩ txs = some st) ↔
        BitcoinBlockV2.TxsSpec f H mtp ltf u fees sigOps txs)
  | [], u, fees, sigOps, undo, _, _ => by simp [connectLoop, TxsSpec]
  | tx :: rest, u, fees, sigOps, undo, hpos, hfees => by
    simp only [List.mem_cons, forall_eq_or_imp] at hpos
    simp only [connectLoop, TxsSpec]
    by_cases hcb : isCoinBase tx = true
    · simp only [hcb, ite_true, Bool.true_eq_false, false_implies, true_and, Bool.not_true, Bool.false_and,
        Bool.false_eq_true, ite_false]
      by_cases hs : MAX_BLOCK_SIGOPS_COST < sigOps + txSigOpCost f u tx
      · simp only [hs, ite_true, reduceCtorEq, exists_false, false_iff, not_and]; intro; omega
      · simp only [hs, ite_false]
        rw [connectLoop_iff' f H mtp ltf rest _ fees _ undo hpos.2 hfees]
        constructor
        · intro h; exact ⟨by omega, h⟩
        · intro h; exact h.2
    · simp only [hcb, Bool.false_eq_true, ite_false, Bool.not_false, Bool.true_and, true_implies]
      obtain ⟨hi1, hi2⟩ := checkTxInputs_iff u tx H
      cases hct : checkTxInputs u tx H with
      | none =>
        dsimp only
        simp only [reduceCtorEq, exists_false, false_iff, not_and]
        intro ⟨⟨ha, hv, ho, _, _⟩, _⟩
        have : ∃ fee, checkTxInputs u tx H = some fee := hi1.2 ⟨ha, hv, ho, by
          have := hpos.1; omega⟩
        rw [hct] at this; obtain ⟨_, h⟩ := this; cases h
      | some fee =>
        dsimp only
        have hfee := hi2 fee hct; subst hfee
        have hspec := hi1.1 ⟨_, hct⟩
        have hfee0 : 0 ≤ feeOf u tx := by unfold feeOf; have := hpos.1; omega
        by_cases hr : moneyRange (fees + feeOf u tx) = true
        · simp only [hr, Bool.not_true, Bool.false_eq_true, ite_false]
          unfold moneyRange at hr; simp only [decide_eq_true_eq] at hr
          by_cases hseq : sequenceLocksOk u H mtp ltf tx = true
          · simp only [hseq, Bool.not_true, Bool.false_eq_true, ite_false]
            by_cases hs : MAX_BLOCK_SIGOPS_COST < sigOps + txSigOpCost f u tx
            · simp only [hs, ite_true, reduceCtorEq, exists_false, false_iff, not_and]; intro _ h; omega
            · simp only [hs, ite_false]
              by_cases hsc : inputScriptsOk f u tx = true
              · simp only [hsc, Bool.not_true, Bool.false_eq_true, ite_false]
                rw [connectLoop_iff' f H mtp ltf rest _ _ _ _ hpos.2 (by omega)]
                rw [sequenceLocks_iff] at hseq
                rw [inputScriptsOk_iff] at hsc
                constructor
                · intro h
                  exact ⟨⟨⟨hspec.1, hspec.2.1, hspec.2.2.1, hseq, hsc⟩, hr.2⟩, by omega, h⟩
                · intro h; exact h.2.2
              · simp only [Bool.not_eq_true] at hsc
                simp only [hsc, Bool.not_false, ite_true, reduceCtorEq, exists_false, false_iff, not_and]
                intro ⟨⟨_, _, _, _, hsc'⟩, _⟩
                rw [← inputScriptsOk_iff] at hsc'; rw [hsc] at hsc'; cases hsc'
          · simp only [Bool.not_eq_true] at hseq
            simp only [hseq, Bool.not_false, ite_true, reduceCtorEq, exists_false, false_iff, not_and]
            intro ⟨⟨_, _, _, hseq', _⟩, _⟩
            rw [← sequenceLocks_iff] at hseq'; rw [hseq] at hseq'; cases hseq'
        · simp only [Bool.not_eq_true] at hr
          simp only [hr, Bool.not_false, ite_true, reduceCtorEq, exists_false, false_iff, not_and]
          unfold moneyRange at hr; simp only [decide_eq_false_iff_not, not_and] at hr
          intro ⟨_, h⟩ _ _; exact hr (by omega) h

/-- The loop's result is the declarative ledger and fee total. -/
private theorem connectLoop_result (f : BitcoinActivation.ScriptFlags) (H : Nat) (mtp : Nat → Nat) (ltf : Nat) :
    ∀ (txs : List BitcoinSer.Tx) (u : Ledger) (fees : Int) (sigOps : Nat) (undo : BlockUndo) (st : LoopState),
      BitcoinBlockV2.connectLoop f H mtp ltf ⟨u, fees, sigOps, undo⟩ txs = some st →
      st.utxo = BitcoinBlockV2.applyTxs H u txs ∧ st.fees = fees + BitcoinBlockV2.totalFees H u txs
  | [], u, fees, sigOps, undo, st, h => by
    simp only [connectLoop, Option.some.injEq] at h; subst h; simp [applyTxs, totalFees]
  | tx :: rest, u, fees, sigOps, undo, st, h => by
    simp only [connectLoop] at h
    simp only [applyTxs, totalFees]
    by_cases hcb : isCoinBase tx = true
    · simp only [hcb, ite_true] at h
      split at h
      · cases h
      · split at h
        · cases h
        · have := connectLoop_result f H mtp ltf rest _ _ _ _ st h
          simp only [hcb, ite_true, Int.zero_add]
          exact this
    · simp only [hcb, Bool.false_eq_true, ite_false] at h
      cases hct : checkTxInputs u tx H with
      | none => rw [hct] at h; cases h
      | some fee =>
        rw [hct] at h
        dsimp only at h
        have hfee := (checkTxInputs_iff u tx H).2 fee hct; subst hfee
        by_cases hr : (!moneyRange (fees + feeOf u tx)) = true
        · rw [if_pos hr] at h; cases h
        · rw [if_neg hr] at h
          by_cases hseq : (!sequenceLocksOk u H mtp ltf tx) = true
          · rw [if_pos hseq] at h; cases h
          · rw [if_neg hseq] at h
            dsimp only at h
            by_cases hs : MAX_BLOCK_SIGOPS_COST < sigOps + txSigOpCost f u tx
            · rw [if_pos hs] at h; cases h
            · rw [if_neg hs] at h
              simp only [Bool.not_false, Bool.true_and] at h
              by_cases hsc : (!inputScriptsOk f u tx) = true
              · rw [if_pos hsc] at h; cases h
              · rw [if_neg hsc] at h
                have := connectLoop_result f H mtp ltf rest _ _ _ _ st h
                simp only [hcb, Bool.false_eq_true, ite_false]
                exact ⟨this.1, by rw [this.2]; omega⟩

private theorem connectBlock_loop_part (S : ChainState) (b : BitcoinSer.Block) (hne : b.vtx ≠ [])
    (hpos : ∀ tx ∈ b.vtx, 0 ≤ BitcoinBlockV2.valueOut tx) :
    (∃ r, (match connectLoop (BitcoinActivation.blockScriptFlags S.nextHeight (scriptException (BitcoinSer.headerHash b.header)))
          S.nextHeight S.mtpNat (BitcoinActivation.lockTimeFlags S.nextHeight) ⟨S.utxo, 0, 0, []⟩ b.vtx with
      | none => none
      | some st =>
        if valueOut (b.vtx.headD BitcoinSer.genesisCoinbase) >
             st.fees + (BitcoinSubsidy.coreSubsidy S.nextHeight : Int) then none
        else some (st.utxo, st.undo)) = some r) ↔
    (TxsSpec (BitcoinActivation.blockScriptFlags S.nextHeight (scriptException (BitcoinSer.headerHash b.header)))
        S.nextHeight S.mtpNat (BitcoinActivation.lockTimeFlags S.nextHeight) S.utxo 0 0 b.vtx ∧
     ∀ cb ∈ b.vtx.take 1,
       valueOut cb ≤ totalFees S.nextHeight S.utxo b.vtx + (BitcoinSubsidy.specSubsidy S.nextHeight : Int)) := by
  cases hl : connectLoop (BitcoinActivation.blockScriptFlags S.nextHeight (scriptException (BitcoinSer.headerHash b.header)))
      S.nextHeight S.mtpNat (BitcoinActivation.lockTimeFlags S.nextHeight) ⟨S.utxo, 0, 0, []⟩ b.vtx with
  | none =>
    dsimp only
    simp only [reduceCtorEq, exists_false, false_iff, not_and]
    intro hspec
    have := (connectLoop_iff _ _ _ _ b.vtx S.utxo 0 0 [] hpos (Int.le_refl 0)).2 hspec
    rw [hl] at this; obtain ⟨_, h⟩ := this; cases h
  | some st =>
    dsimp only
    have hspec := (connectLoop_iff _ _ _ _ b.vtx S.utxo 0 0 [] hpos (Int.le_refl 0)).1 ⟨_, hl⟩
    have hres := connectLoop_result _ _ _ _ b.vtx S.utxo 0 0 [] st hl
    simp only [hspec, true_and]
    rw [hres.2, Int.zero_add, BitcoinSubsidy.core_eq_spec]
    obtain ⟨hd, vtx⟩ := b
    cases vtx with
    | nil => exact absurd rfl hne
    | cons cb rest =>
      simp only [List.headD_cons, List.take_succ_cons, List.take_zero, List.mem_singleton, forall_eq]
      by_cases hgt : valueOut cb > totalFees S.nextHeight S.utxo (cb :: rest) + (BitcoinSubsidy.specSubsidy S.nextHeight : Int)
      · simp only [hgt, ite_true, reduceCtorEq, exists_false, false_iff]; omega
      · simp only [hgt, ite_false, Option.some.injEq, exists_eq', true_iff]; omega

private theorem headerSpec_iff (S : ChainState) (h : BitcoinSer.Header) (now : Int) :
    BitcoinBlockV2.acceptHeader S h now = .accept S [] ↔ BitcoinBlockV2.HeaderSpec S h now := by
  rw [acceptHeader_eq_iff]
  unfold HeaderSpec checkHeaderPow
  rw [BitcoinPow.checkProofOfWork_iff]
  have hv := BitcoinHeader.versionOutdated_iff h.version S.tipHeight
  constructor
  · rintro ⟨a, b, c, d, e, f⟩
    refine ⟨a, b, c, by omega, by omega, ?_⟩
    rw [← hv]; simp [f]
  · rintro ⟨a, b, c, d, e, f⟩
    refine ⟨a, b, c, by omega, by omega, ?_⟩
    rw [← hv] at f; simpa using f

private theorem acceptHeader_cases (S : ChainState) (h : BitcoinSer.Header) (now : Int) :
    BitcoinBlockV2.acceptHeader S h now = .accept S [] ∨ BitcoinBlockV2.acceptHeader S h now = .invalid ∨
    BitcoinBlockV2.acceptHeader S h now = .futureTime ∨ BitcoinBlockV2.acceptHeader S h now = .missingPrev := by
  unfold acceptHeader
  repeat' split
  all_goals simp

private theorem validate_accept_iff (S : ChainState) (b : BitcoinSer.Block) (now : Int)
    (ha : BitcoinBlockV2.acceptHeader S b.header now = .accept S []) :
    (∃ S' undo, BitcoinBlockV2.validate S b now = .accept S' undo) ↔
      BitcoinBlockV2.checkBlock b = true ∧ BitcoinBlockV2.contextualCheckBlock S b = true ∧
      ∃ r, BitcoinBlockV2.connectBlock S b = some r := by
  unfold validate
  rw [ha]
  simp only [Bool.not_eq_true']
  by_cases hcb : checkBlock b = false
  · rw [if_pos hcb]
    simp only [reduceCtorEq, exists_false, false_iff, not_and]
    intro h; rw [hcb] at h; cases h
  · rw [if_neg hcb]
    have hcb' : checkBlock b = true := by simpa using hcb
    simp only [hcb', true_and]
    by_cases hcc : contextualCheckBlock S b = false
    · rw [if_pos hcc]
      simp only [reduceCtorEq, exists_false, false_iff, not_and]
      intro h; rw [hcc] at h; cases h
    · rw [if_neg hcc]
      have hcc' : contextualCheckBlock S b = true := by simpa using hcc
      simp only [hcc', true_and]
      cases connectBlock S b with
      | none => simp
      | some r => simp

private theorem getCoin_spendCoin : ∀ (u : Ledger) (op op' : BitcoinSer.OutPoint),
    BitcoinBlockV2.getCoin (BitcoinBlockV2.spendCoin u op) op' = if op' = op then none else BitcoinBlockV2.getCoin u op'
  | [], op, op' => by simp [spendCoin, getCoin]
  | (k, c) :: rest, op, op' => by
    simp only [spendCoin, getCoin]
    by_cases hk : k = op
    · rw [if_pos hk, getCoin_spendCoin rest op op']
      by_cases h' : op' = op
      · simp [h']
      · simp only [h', ite_false]
        rw [if_neg (by rw [hk]; exact fun e => h' e.symm)]
    · rw [if_neg hk]
      simp only [getCoin]
      by_cases h' : k = op'
      · rw [if_pos h', if_pos h']
        rw [if_neg (by rw [← h']; exact hk)]
      · rw [if_neg h', if_neg h', getCoin_spendCoin rest op op']

private theorem getCoin_addCoin (u : Ledger) (op : BitcoinSer.OutPoint) (c : Coin) (op' : BitcoinSer.OutPoint) :
    BitcoinBlockV2.getCoin (BitcoinBlockV2.addCoin u op c) op' =
      if BitcoinBlockV2.isUnspendable c.out.scriptPubKey then BitcoinBlockV2.getCoin u op'
      else if op' = op then some c else BitcoinBlockV2.getCoin u op' := by
  unfold addCoin
  by_cases hu : isUnspendable c.out.scriptPubKey = true
  · simp [hu]
  · simp only [hu, Bool.false_eq_true, ite_false, getCoin, getCoin_spendCoin]
    by_cases h' : op' = op
    · simp [h']
    · simp only [h', ite_false]
      rw [if_neg (fun e => h' e.symm)]

private theorem getCoin_spendInputs : ∀ (ins : List BitcoinSer.TxIn) (u : Ledger) (op : BitcoinSer.OutPoint),
    BitcoinBlockV2.getCoin (BitcoinBlockV2.spendInputs u ins) op =
      if ins.any (fun i => i.prevout = op) then none else BitcoinBlockV2.getCoin u op
  | [], u, op => by simp [spendInputs]
  | i :: rest, u, op => by
    simp only [spendInputs, List.any_cons, Bool.or_eq_true, decide_eq_true_eq]
    rw [getCoin_spendInputs rest]
    by_cases h1 : (rest.any fun i => i.prevout = op) = true
    · simp [h1]
    · simp only [h1, Bool.false_eq_true, or_false, ite_false]
      rw [getCoin_spendCoin]
      by_cases h2 : i.prevout = op
      · simp [h2]
      · simp only [h2, ite_false]; rw [if_neg (fun e => h2 e.symm)]

private theorem outPoint_eq_iff (op : BitcoinSer.OutPoint) (h : BitcoinSer.Bytes) (n : Nat) :
    op = ⟨h, n⟩ ↔ op.hash = h ∧ op.n = n := by
  cases op; simp

private theorem getCoin_addCoinsFrom (txid : BitcoinSer.Bytes) (H : Nat) (cb : Bool) :
    ∀ (os : List BitcoinSer.TxOut) (u : Ledger) (i : Nat) (op : BitcoinSer.OutPoint),
    BitcoinBlockV2.getCoin (BitcoinBlockV2.addCoinsFrom txid H cb u i os) op =
      if op.hash = txid ∧ i ≤ op.n ∧ op.n < i + os.length ∧
          BitcoinBlockV2.isUnspendable (os.getD (op.n - i) ⟨0, []⟩).scriptPubKey = false
      then some ⟨os.getD (op.n - i) ⟨0, []⟩, H, cb⟩ else BitcoinBlockV2.getCoin u op
  | [], u, i, op => by
    simp only [addCoinsFrom, List.length_nil, Nat.add_zero]
    rw [if_neg (by omega)]
  | o :: rest, u, i, op => by
    simp only [addCoinsFrom]
    rw [getCoin_addCoinsFrom txid H cb rest]
    simp only [List.length_cons]
    by_cases hin : op.hash = txid ∧ i + 1 ≤ op.n ∧ op.n < i + 1 + rest.length ∧
        isUnspendable (rest.getD (op.n - (i + 1)) ⟨0, []⟩).scriptPubKey = false
    · rw [if_pos hin]
      have e : (o :: rest).getD (op.n - i) ⟨0, []⟩ = rest.getD (op.n - (i + 1)) ⟨0, []⟩ := by
        obtain ⟨k, hk⟩ : ∃ k, op.n - i = k + 1 := ⟨op.n - (i + 1), by omega⟩
        rw [hk, List.getD_cons_succ]; congr 1; omega
      rw [if_pos ⟨hin.1, by omega, by omega, by rw [e]; exact hin.2.2.2⟩, e]
    · rw [if_neg hin]
      rw [getCoin_addCoin]
      by_cases hop : op = ⟨txid, i⟩
      · have hh : op.hash = txid := by rw [hop]
        have hn' : op.n = i := by rw [hop]
        have hn : op.n - i = 0 := by omega
        rw [hn, List.getD_cons_zero]
        by_cases hu : isUnspendable o.scriptPubKey = true
        · rw [if_pos hu, if_neg (by simp [hu])]
        · simp only [Bool.not_eq_true] at hu
          rw [if_neg (by simp [hu]), if_pos hop, if_pos ⟨hh, by omega, by omega, hu⟩]
      · have hop' : ¬ (op.hash = txid ∧ op.n = i) := fun h => hop ((outPoint_eq_iff op txid i).2 h)
        have hneg : ¬ (op.hash = txid ∧ i ≤ op.n ∧ op.n < i + (rest.length + 1) ∧
            isUnspendable ((o :: rest).getD (op.n - i) ⟨0, []⟩).scriptPubKey = false) := by
          intro h; apply hin
          have hn : op.n ≠ i := fun hn => hop' ⟨h.1, hn⟩
          obtain ⟨k, hk⟩ : ∃ k, op.n - i = k + 1 := ⟨op.n - (i + 1), by omega⟩
          have h4 := h.2.2.2; rw [hk, List.getD_cons_succ] at h4
          refine ⟨h.1, by omega, by omega, ?_⟩
          rw [show op.n - (i + 1) = k by omega]; exact h4
        rw [if_neg hneg]
        split
        · rfl
        · (try rw [if_neg hop]); (try rfl)

private theorem getCoin_mem : ∀ (u : Ledger) (op : BitcoinSer.OutPoint) (c : Coin),
    BitcoinBlockV2.getCoin u op = some c → (op, c) ∈ u
  | [], _, _, h => by cases h
  | (k, c') :: rest, op, c, h => by
    simp only [getCoin] at h
    by_cases hk : k = op
    · rw [if_pos hk] at h; simp only [Option.some.injEq] at h; subst hk; subst h; simp
    · rw [if_neg hk] at h; exact List.mem_cons_of_mem _ (getCoin_mem rest op c h)

private theorem mem_keys_iff : ∀ (u : Ledger) (op : BitcoinSer.OutPoint),
    op ∈ u.map Prod.fst ↔ (BitcoinBlockV2.getCoin u op).isSome = true
  | [], op => by simp [getCoin]
  | (k, c) :: rest, op => by
    simp only [List.map_cons, List.mem_cons, getCoin]
    by_cases hk : k = op
    · simp [hk]
    · rw [if_neg hk, mem_keys_iff rest]
      constructor
      · rintro (h | h)
        · exact absurd h.symm hk
        · exact h
      · intro h; exact Or.inr h

private theorem spendCoin_sublist : ∀ (u : Ledger) (op : BitcoinSer.OutPoint), (BitcoinBlockV2.spendCoin u op).Sublist u
  | [], _ => List.Sublist.refl _
  | (k, c) :: rest, op => by
    simp only [spendCoin]
    by_cases hk : k = op
    · rw [if_pos hk]; exact (spendCoin_sublist rest op).cons _
    · rw [if_neg hk]; exact (spendCoin_sublist rest op).cons₂ _

private theorem keysNodup_spendCoin (u : Ledger) (op : BitcoinSer.OutPoint) (h : BitcoinBlockV2.keysNodup u) :
    BitcoinBlockV2.keysNodup (BitcoinBlockV2.spendCoin u op) :=
  h.sublist ((spendCoin_sublist u op).map _)

private theorem keysNodup_addCoin (u : Ledger) (op : BitcoinSer.OutPoint) (c : Coin) (h : BitcoinBlockV2.keysNodup u) :
    BitcoinBlockV2.keysNodup (BitcoinBlockV2.addCoin u op c) := by
  unfold addCoin
  split
  · exact h
  · unfold keysNodup
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, keysNodup_spendCoin u op h⟩
    rw [mem_keys_iff, getCoin_spendCoin]; simp

/-- `LedgerOk` is preserved by `SpendCoin`. -/
private theorem ledgerOk_spendCoin (u : Ledger) (op : BitcoinSer.OutPoint) (h : BitcoinBlockV2.LedgerOk u) :
    BitcoinBlockV2.LedgerOk (BitcoinBlockV2.spendCoin u op) :=
  ⟨keysNodup_spendCoin u op h.1, fun e he => h.2 e ((spendCoin_sublist u op).subset he)⟩

private theorem ledgerOk_spendInputs : ∀ (ins : List BitcoinSer.TxIn) (u : Ledger), BitcoinBlockV2.LedgerOk u →
    BitcoinBlockV2.LedgerOk (BitcoinBlockV2.spendInputs u ins)
  | [], u, h => h
  | i :: rest, u, h => ledgerOk_spendInputs rest _ (ledgerOk_spendCoin u i.prevout h)

private theorem ledgerOk_addCoin (u : Ledger) (op : BitcoinSer.OutPoint) (c : Coin) (h : BitcoinBlockV2.LedgerOk u)
    (hc : c.height ≠ 0) : BitcoinBlockV2.LedgerOk (BitcoinBlockV2.addCoin u op c) := by
  refine ⟨keysNodup_addCoin u op c h.1, ?_⟩
  unfold addCoin
  intro e he
  split at he
  · exact h.2 e he
  · rename_i hu
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨hc, by simpa using hu⟩
    · exact h.2 e ((spendCoin_sublist u op).subset he)

private theorem ledgerOk_addCoinsFrom (txid : BitcoinSer.Bytes) (H : Nat) (cb : Bool) (hH : H ≠ 0) :
    ∀ (os : List BitcoinSer.TxOut) (u : Ledger) (i : Nat), BitcoinBlockV2.LedgerOk u →
    BitcoinBlockV2.LedgerOk (BitcoinBlockV2.addCoinsFrom txid H cb u i os)
  | [], u, _, h => h
  | o :: rest, u, i, h => ledgerOk_addCoinsFrom txid H cb hH rest _ (i + 1) (ledgerOk_addCoin u _ _ h hH)

/-- `UpdateCoins` at a positive height preserves the ledger invariant. -/
private theorem ledgerOk_updateCoins (u : Ledger) (tx : BitcoinSer.Tx) (H : Nat) (hH : H ≠ 0)
    (h : BitcoinBlockV2.LedgerOk u) : BitcoinBlockV2.LedgerOk (BitcoinBlockV2.updateCoins u tx H) := by
  unfold updateCoins
  apply ledgerOk_addCoinsFrom _ _ _ hH
  split
  · exact h
  · exact ledgerOk_spendInputs _ _ h

private theorem ledgerOk_applyTxs (H : Nat) (hH : H ≠ 0) : ∀ (txs : List BitcoinSer.Tx) (u : Ledger),
    BitcoinBlockV2.LedgerOk u → BitcoinBlockV2.LedgerOk (BitcoinBlockV2.applyTxs H u txs)
  | [], u, h => h
  | tx :: rest, u, h => ledgerOk_applyTxs H hH rest _ (ledgerOk_updateCoins u tx H hH h)

/-- Heights of coins after `UpdateCoins` at height `H`: old coins keep their heights, new ones get `H`. -/
private theorem heights_updateCoins (u : Ledger) (tx : BitcoinSer.Tx) (H T : Nat) (hT : T ≤ H)
    (h : ∀ e ∈ u, e.2.height ≤ T) : ∀ e ∈ BitcoinBlockV2.updateCoins u tx H, e.2.height ≤ H := by
  unfold updateCoins
  have base : ∀ e ∈ (if isCoinBase tx = true then u else spendInputs u tx.vin), e.2.height ≤ H := by
    split
    · intro e he; exact Nat.le_trans (h e he) hT
    · intro e he
      have : ∀ (ins : List BitcoinSer.TxIn) (v : Ledger), (∀ e ∈ v, e.2.height ≤ H) →
          ∀ e ∈ spendInputs v ins, e.2.height ≤ H := by
        intro ins
        induction ins with
        | nil => intro v hv; exact hv
        | cons i rest ih =>
          intro v hv e he
          exact ih _ (fun e he => hv e ((spendCoin_sublist v i.prevout).subset he)) e he
      exact this tx.vin u (fun e he => Nat.le_trans (h e he) hT) e he
  generalize (if isCoinBase tx = true then u else spendInputs u tx.vin) = v at base
  have : ∀ (os : List BitcoinSer.TxOut) (v : Ledger) (i : Nat), (∀ e ∈ v, e.2.height ≤ H) →
      ∀ e ∈ addCoinsFrom (BitcoinSer.txid tx) H (isCoinBase tx) v i os, e.2.height ≤ H := by
    intro os
    induction os with
    | nil => intro v i hv; exact hv
    | cons o rest ih =>
      intro v i hv
      apply ih
      intro e he
      unfold addCoin at he
      split at he
      · exact hv e he
      · simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact Nat.le_refl _
        · exact hv e ((spendCoin_sublist v _).subset he)
  exact this tx.vout v 0 base

private theorem heights_applyTxs (H : Nat) : ∀ (txs : List BitcoinSer.Tx) (u : Ledger), (∀ e ∈ u, e.2.height ≤ H) →
    ∀ e ∈ BitcoinBlockV2.applyTxs H u txs, e.2.height ≤ H
  | [], u, h => h
  | tx :: rest, u, h => heights_applyTxs H rest _ (heights_updateCoins u tx H H (Nat.le_refl _) h)

/-- **Reachable states are well formed:** the genesis header first, distinct keys, and every coin
spendable and created at a height between 1 and the tip. -/
theorem solution (S : ChainState) (h : BitcoinBlockV2.Reachable S) :
    BitcoinBlockV2.WellFormed S := by
  induction h with
  | genesis => exact initial_wellFormed
  | @step S b now S' undo _ hv ih =>
    rw [apply_spec S b now S' undo hv]
    obtain ⟨hhead, hnd, hcoins⟩ := ih
    have hne : S.headers ≠ [] := by intro e; rw [e] at hhead; cases hhead
    have hH : S.nextHeight ≠ 0 := by
      unfold ChainState.nextHeight; intro e; exact hne (List.eq_nil_of_length_eq_zero e)
    have hok : LedgerOk S.utxo := ⟨hnd, fun e he => ⟨by have := (hcoins e he).1; omega, (hcoins e he).2.2⟩⟩
    have htip : S.tipHeight ≤ S.nextHeight := by unfold ChainState.tipHeight ChainState.nextHeight; omega
    have hhead' : (S.headers ++ [b.header]).head? = some BitcoinSer.genesisHeader := by
      obtain ⟨x, xs, hx⟩ : ∃ x xs, S.headers = x :: xs := by
        cases hS : S.headers with
        | nil => exact absurd hS hne
        | cons x xs => exact ⟨x, xs, rfl⟩
      rw [hx] at hhead ⊢; simpa using hhead
    have htip' : ChainState.tipHeight ⟨S.headers ++ [b.header], (applySpec S b).utxo⟩ = S.nextHeight := by
      unfold ChainState.tipHeight ChainState.nextHeight; simp
    unfold applySpec
    split
    · refine ⟨hhead', hnd, ?_⟩
      intro e he
      have := hcoins e he
      exact ⟨this.1, by unfold ChainState.tipHeight ChainState.nextHeight at *; simp; omega, this.2.2⟩
    · have hok' := ledgerOk_applyTxs S.nextHeight hH b.vtx S.utxo hok
      have hts := heights_applyTxs S.nextHeight b.vtx S.utxo (fun e he => Nat.le_trans (hcoins e he).2.1 htip)
      refine ⟨hhead', hok'.1, ?_⟩
      intro e he
      refine ⟨by have := (hok'.2 e he).1; omega, ?_, (hok'.2 e he).2⟩
      unfold ChainState.tipHeight ChainState.nextHeight at *
      simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
      exact hts e he

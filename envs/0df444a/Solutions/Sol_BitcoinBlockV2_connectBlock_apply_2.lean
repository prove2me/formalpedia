-- Prove2me | solution 2 for BitcoinBlockV2.connectBlock_apply
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-28T15:24:15.836808+00:00
-- url     : https://prove2.me/submissions/820a150f-7513-4e81-bc99-7bb46280a167

import Definitions.Def_BitcoinBlockV2
import Theorems.Thm_BitcoinPow_checkProofOfWork_iff
import Theorems.Thm_BitcoinHeader_versionOutdated_iff
import Theorems.Thm_BitcoinSubsidy_core_eq_spec
import Theorems.Thm_BitcoinBIP68_fold_acceptance
import Theorems.Thm_BitcoinBIP68_decode_sequence
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

/-- An accepted block's ledger is the declarative one. -/
theorem solution (S : ChainState) (b : BitcoinSer.Block) (u : Ledger) (undo : BlockUndo)
    (h : BitcoinBlockV2.connectBlock S b = some (u, undo)) : u = (BitcoinBlockV2.applySpec S b).utxo := by
  unfold connectBlock at h
  unfold applySpec
  simp only at h
  by_cases hg : BitcoinSer.headerHash b.header = BitcoinSer.genesisHash
  · simp only [hg, ite_true, Option.some.injEq, Prod.mk.injEq] at h; simp [hg, h.1]
  · simp only [hg, ite_false] at h ⊢
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i st hl
        split at h
        · cases h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]
          exact (connectLoop_result _ _ _ _ b.vtx S.utxo 0 0 [] st hl).1

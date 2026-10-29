-- Prove2me | solution 2 for BitcoinReorg.connectChain_reachable
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T02:58:54.869181+00:00
-- url     : https://prove2.me/submissions/4355bc0b-4f34-445d-8969-924285c45b45

import Definitions.Def_BitcoinReorg
import Theorems.Thm_BitcoinBlockV2_checkBlock_iff
import Theorems.Thm_BitcoinBlockV2_checkTxInputs_iff
import Theorems.Thm_BitcoinBlockV2_reachable_wellFormed
import Theorems.Thm_BitcoinBlockV2_apply_spec
import Theorems.Thm_BitcoinReorg_updateCoins_equiv

open BitcoinReorg BitcoinBlockV2

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

private theorem acceptHeader_cases (S : ChainState) (h : BitcoinSer.Header) (now : Int) :
    BitcoinBlockV2.acceptHeader S h now = .accept S [] ∨ BitcoinBlockV2.acceptHeader S h now = .invalid ∨
    BitcoinBlockV2.acceptHeader S h now = .futureTime ∨ BitcoinBlockV2.acceptHeader S h now = .missingPrev := by
  unfold acceptHeader
  repeat' split
  all_goals simp

/-- **Apply-spec equality.** Every accepted block yields the declaratively specified state. -/
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
private theorem disconnectTxs_append (H : Nat) (exc : Bool) :
    ∀ (l1 l2 : List (BitcoinSer.Tx × Option (List Coin))) (v : Ledger),
    BitcoinBlockV2.disconnectTxs H exc v (l1 ++ l2) =
      match BitcoinBlockV2.disconnectTxs H exc v l1 with
      | none => none
      | some (v', c1) =>
        match BitcoinBlockV2.disconnectTxs H exc v' l2 with
        | none => none
        | some (v'', c2) => some (v'', c1 && c2)
  | [], l2, v => by
    simp only [List.nil_append, disconnectTxs]
    cases disconnectTxs H exc v l2 with
    | none => rfl
    | some r => obtain ⟨w, c⟩ := r; simp
  | (tx, undo) :: rest, l2, v => by
    simp only [List.cons_append, disconnectTxs]
    cases disconnectTx v H exc tx undo with
    | none => rfl
    | some p =>
      obtain ⟨v', c⟩ := p
      simp only
      rw [disconnectTxs_append H exc rest l2 v']
      cases disconnectTxs H exc v' rest with
      | none => rfl
      | some q =>
        obtain ⟨v'', c'⟩ := q
        simp only
        cases disconnectTxs H exc v'' l2 with
        | none => rfl
        | some r => obtain ⟨w, c''⟩ := r; simp [Bool.and_assoc]

/-- Spending back the outputs a transaction added, when none of them pre-existed, yields the ledger
before the addition, cleanly. -/
private theorem spendOutputs_restore (txid : BitcoinSer.Bytes) (H : Nat) (cb exc : Bool) (base : Ledger)
    (hfresh : ∀ n, BitcoinBlockV2.getCoin base ⟨txid, n⟩ = none) :
    ∀ (os : List BitcoinSer.TxOut) (i : Nat) (v : Ledger),
      BitcoinBlockV2.Equiv v (BitcoinBlockV2.addCoinsFrom txid H cb base i os) →
      ∃ v1, BitcoinBlockV2.spendOutputs v txid H cb exc os i = (v1, true) ∧ BitcoinBlockV2.Equiv v1 base
  | [], i, v, hv => ⟨v, rfl, by simpa [addCoinsFrom] using hv⟩
  | o :: rest, i, v, hv => by
    simp only [spendOutputs]
    simp only [addCoinsFrom] at hv
    by_cases hu : isUnspendable o.scriptPubKey = true
    · have hv' : Equiv v (addCoinsFrom txid H cb base (i + 1) rest) := by
        intro op; rw [hv op]
        have : addCoin base ⟨txid, i⟩ ⟨o, H, cb⟩ = base := by unfold addCoin; simp [hu]
        rw [this]
      obtain ⟨v1, h1, h2⟩ := spendOutputs_restore txid H cb exc base hfresh rest (i + 1) v hv'
      rw [if_pos hu]
      simp only [h1]
      exact ⟨v1, rfl, h2⟩
    · simp only [Bool.not_eq_true] at hu
      have hget : getCoin v ⟨txid, i⟩ = some ⟨o, H, cb⟩ := by
        rw [hv, getCoin_addCoinsFrom]
        rw [if_neg (by simp; omega), getCoin_addCoin]
        simp [hu]
      have hv' : Equiv (spendCoin v ⟨txid, i⟩) (addCoinsFrom txid H cb base (i + 1) rest) := by
        intro op
        rw [getCoin_spendCoin, hv op, getCoin_addCoinsFrom, getCoin_addCoinsFrom]
        by_cases hop : op = ⟨txid, i⟩
        · rw [if_pos hop, hop]
          simp only [true_and]
          rw [if_neg (by omega), hfresh]
        · rw [if_neg hop]
          split
          · rfl
          · rw [getCoin_addCoin]
            simp only [hu, Bool.false_eq_true, ite_false]
            rw [if_neg hop]
      obtain ⟨v1, h1, h2⟩ := spendOutputs_restore txid H cb exc base hfresh rest (i + 1) _ hv'
      rw [if_neg (by simp [hu])]
      simp only [hget, decide_true, Bool.and_self, Bool.true_or, h1]
      exact ⟨v1, rfl, h2⟩

/-- Restoring the inputs a transaction spent (in reverse order, as `DisconnectBlock` does) yields the
ledger before the spends, cleanly. -/
private theorem restoreInputs_restore : ∀ (vin : List BitcoinSer.TxIn) (u v1 : Ledger),
    (vin.map BitcoinSer.TxIn.prevout).Nodup → (∀ i ∈ vin, (BitcoinBlockV2.getCoin u i.prevout).isSome = true) →
    BitcoinBlockV2.LedgerOk u → BitcoinBlockV2.Equiv v1 (BitcoinBlockV2.spendInputs u vin) →
    ∃ w, BitcoinBlockV2.restoreInputs v1 (vin.zip (vin.map fun i => BitcoinBlockV2.accessCoin u i.prevout)) = some (w, true) ∧
      BitcoinBlockV2.Equiv w u
  | [], u, v1, _, _, _, hv => ⟨v1, rfl, hv⟩
  | i :: rest, u, v1, hnd, hex, hok, hv => by
    simp only [List.map_cons, List.zip_cons_cons, restoreInputs]
    have hnd' : (rest.map BitcoinSer.TxIn.prevout).Nodup := (List.nodup_cons.1 hnd).2
    have hni : i.prevout ∉ rest.map BitcoinSer.TxIn.prevout := (List.nodup_cons.1 hnd).1
    have hne : ∀ j ∈ rest, j.prevout ≠ i.prevout := by
      intro j hj e; exact hni (List.mem_map.2 ⟨j, hj, e⟩)
    have hex' : ∀ j ∈ rest, (getCoin (spendCoin u i.prevout) j.prevout).isSome = true := by
      intro j hj; rw [getCoin_spendCoin, if_neg (hne j hj)]; exact hex j (by simp [hj])
    have hmap : rest.map (fun j => accessCoin u j.prevout) = rest.map (fun j => accessCoin (spendCoin u i.prevout) j.prevout) := by
      apply List.map_congr_left; intro j hj; unfold accessCoin; rw [getCoin_spendCoin, if_neg (hne j hj)]
    rw [hmap]
    have hv' : Equiv v1 (spendInputs (spendCoin u i.prevout) rest) := by simpa [spendInputs] using hv
    obtain ⟨w1, h1, h2⟩ := restoreInputs_restore rest (spendCoin u i.prevout) v1 hnd' hex' (ledgerOk_spendCoin u _ hok) hv'
    rw [h1]
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (hex i (by simp))
    have hacc : accessCoin u i.prevout = c := by unfold accessCoin; rw [hc]; rfl
    rw [hacc]
    have hmem := getCoin_mem u _ c hc
    have hc0 : c.height ≠ 0 := (hok.2 _ hmem).1
    have hsp : isUnspendable c.out.scriptPubKey = false := (hok.2 _ hmem).2
    have hw1 : getCoin w1 i.prevout = none := by rw [h2, getCoin_spendCoin, if_pos rfl]
    unfold applyTxInUndo
    simp only [haveCoin, hw1, Option.isSome_none, Bool.not_false, hc0, ite_false]
    refine ⟨addCoin w1 i.prevout c, rfl, ?_⟩
    intro op; rw [getCoin_addCoin, hsp]; simp only [Bool.false_eq_true, ite_false]
    by_cases hop : op = i.prevout
    · rw [if_pos hop, hop, hc]
    · rw [if_neg hop, h2, getCoin_spendCoin, if_neg hop]

/-- Undoing a non-coinbase transaction with its undo data restores the ledger it was applied to. -/
private theorem disconnectTx_restore (u : Ledger) (H : Nat) (exc : Bool) (tx : BitcoinSer.Tx) (v : Ledger)
    (hcb : BitcoinBlockV2.isCoinBase tx = false) (hnd : (tx.vin.map BitcoinSer.TxIn.prevout).Nodup)
    (hex : ∀ i ∈ tx.vin, (BitcoinBlockV2.getCoin u i.prevout).isSome = true) (hok : BitcoinBlockV2.LedgerOk u)
    (hfresh : ∀ n, BitcoinBlockV2.getCoin u ⟨BitcoinSer.txid tx, n⟩ = none)
    (hv : BitcoinBlockV2.Equiv v (BitcoinBlockV2.updateCoins u tx H)) :
    ∃ w, BitcoinBlockV2.disconnectTx v H exc tx (some (BitcoinBlockV2.txUndo u tx)) = some (w, true) ∧ BitcoinBlockV2.Equiv w u := by
  unfold disconnectTx
  simp only [hcb, Bool.false_and]
  have hfresh' : ∀ n, getCoin (spendInputs u tx.vin) ⟨BitcoinSer.txid tx, n⟩ = none := by
    intro n; rw [getCoin_spendInputs]; split
    · rfl
    · exact hfresh n
  have hv' : Equiv v (addCoinsFrom (BitcoinSer.txid tx) H false (spendInputs u tx.vin) 0 tx.vout) := by
    unfold updateCoins at hv; simpa [hcb] using hv
  obtain ⟨v1, h1, h2⟩ := spendOutputs_restore (BitcoinSer.txid tx) H false false (spendInputs u tx.vin) hfresh' tx.vout 0 v hv'
  rw [h1]
  simp only [txUndo, List.length_map, ne_eq, not_true_eq_false, ite_false]
  obtain ⟨w, hw, hw2⟩ := restoreInputs_restore tx.vin u v1 hnd hex hok h2
  rw [hw]
  exact ⟨w, rfl, hw2⟩

/-- Undoing the coinbase (no undo data) restores the ledger it was applied to. -/
private theorem disconnectCoinbase_restore (u : Ledger) (H : Nat) (exc : Bool) (tx : BitcoinSer.Tx) (v : Ledger)
    (hcb : BitcoinBlockV2.isCoinBase tx = true)
    (hfresh : ∀ n, BitcoinBlockV2.getCoin u ⟨BitcoinSer.txid tx, n⟩ = none)
    (hv : BitcoinBlockV2.Equiv v (BitcoinBlockV2.updateCoins u tx H)) :
    ∃ w, BitcoinBlockV2.disconnectTx v H exc tx none = some (w, true) ∧ BitcoinBlockV2.Equiv w u := by
  unfold disconnectTx
  simp only [hcb, Bool.true_and]
  have hv' : Equiv v (addCoinsFrom (BitcoinSer.txid tx) H true u 0 tx.vout) := by
    unfold updateCoins at hv; simpa [hcb] using hv
  obtain ⟨v1, h1, h2⟩ := spendOutputs_restore (BitcoinSer.txid tx) H true exc u hfresh tx.vout 0 v hv'
  rw [h1]
  exact ⟨v1, rfl, h2⟩

/-- The transaction loop, undone in reverse with the undo data it produced, restores the ledger. -/
private theorem loop_disconnect (f : BitcoinActivation.ScriptFlags) (H : Nat) (mtp : Nat → Nat) (ltf : Nat) (exc : Bool)
    (hH : H ≠ 0) : ∀ (txs : List BitcoinSer.Tx) (u : Ledger) (fees : Int) (sig : Nat) (undo0 : BlockUndo) (st : LoopState),
    BitcoinBlockV2.connectLoop f H mtp ltf ⟨u, fees, sig, undo0⟩ txs = some st →
    (∀ tx ∈ txs, BitcoinBlockV2.isCoinBase tx = false) → (txs.map BitcoinSer.txid).Nodup →
    (∀ tx ∈ txs, ∀ o, BitcoinBlockV2.getCoin u ⟨BitcoinSer.txid tx, o⟩ = none) → BitcoinBlockV2.LedgerOk u →
    (∀ tx ∈ txs, (tx.vin.map BitcoinSer.TxIn.prevout).Nodup) →
    ∃ us : BlockUndo, st.undo = undo0 ++ us ∧ us.length = txs.length ∧
      ∀ v, BitcoinBlockV2.Equiv v st.utxo →
        ∃ w, BitcoinBlockV2.disconnectTxs H exc v ((txs.zip (us.map some)).reverse) = some (w, true) ∧ BitcoinBlockV2.Equiv w u
  | [], u, fees, sig, undo0, st, h, _, _, _, _, _ => by
    simp only [connectLoop, Option.some.injEq] at h; subst h
    exact ⟨[], by simp, rfl, fun v hv => ⟨v, rfl, hv⟩⟩
  | tx :: rest, u, fees, sig, undo0, st, h, hncb, hnd, hfresh, hok, hpn => by
    simp only [connectLoop] at h
    have hc : isCoinBase tx = false := hncb tx (by simp)
    simp only [hc, Bool.false_eq_true, ite_false] at h
    cases hct : checkTxInputs u tx H with
    | none => rw [hct] at h; cases h
    | some fee =>
      rw [hct] at h; dsimp only at h
      have hex : ∀ i ∈ tx.vin, (getCoin u i.prevout).isSome = true := by
        obtain ⟨hall, _⟩ := ((checkTxInputs_iff u tx H).1).1 ⟨fee, hct⟩
        intro i hi; obtain ⟨c, hc', _⟩ := hall i hi; rw [hc']; rfl
      by_cases hr : (!moneyRange (fees + fee)) = true
      · rw [if_pos hr] at h; cases h
      · rw [if_neg hr] at h
        by_cases hseq : (!sequenceLocksOk u H mtp ltf tx) = true
        · rw [if_pos hseq] at h; cases h
        · rw [if_neg hseq] at h; dsimp only at h
          by_cases hs : MAX_BLOCK_SIGOPS_COST < sig + txSigOpCost f u tx
          · rw [if_pos hs] at h; cases h
          · rw [if_neg hs] at h
            simp only [Bool.not_false, Bool.true_and] at h
            by_cases hsc : (!inputScriptsOk f u tx) = true
            · rw [if_pos hsc] at h; cases h
            · rw [if_neg hsc] at h
              have hnd' : (rest.map BitcoinSer.txid).Nodup := (List.nodup_cons.1 hnd).2
              have hnotin : BitcoinSer.txid tx ∉ rest.map BitcoinSer.txid := (List.nodup_cons.1 hnd).1
              have hfresh' : ∀ tx' ∈ rest, ∀ o, getCoin (updateCoins u tx H) ⟨BitcoinSer.txid tx', o⟩ = none := by
                intro tx' htx' o
                have hne : BitcoinSer.txid tx' ≠ BitcoinSer.txid tx := fun e => hnotin (List.mem_map.2 ⟨tx', htx', e⟩)
                unfold updateCoins; rw [getCoin_addCoinsFrom]
                rw [if_neg (fun hh => hne hh.1)]
                simp only [hc, Bool.false_eq_true, ite_false]
                rw [getCoin_spendInputs]; split
                · rfl
                · exact hfresh tx' (by simp [htx']) o
              obtain ⟨us, hus, hlen, hdis⟩ := loop_disconnect f H mtp ltf exc hH rest (updateCoins u tx H) _ _ _ st h
                (fun t ht => hncb t (by simp [ht])) hnd' hfresh' (ledgerOk_updateCoins u tx H hH hok)
                (fun t ht => hpn t (by simp [ht]))
              refine ⟨txUndo u tx :: us, by rw [hus]; simp, by simp [hlen], ?_⟩
              intro v hv
              obtain ⟨w1, hw1, hw1e⟩ := hdis v hv
              simp only [List.map_cons, List.zip_cons_cons, List.reverse_cons]
              rw [disconnectTxs_append, hw1]
              obtain ⟨w, hw, hwe⟩ := disconnectTx_restore u H exc tx w1 hc (hpn tx (by simp)) hex hok
                (fun n => hfresh tx (by simp) n) hw1e
              simp only [disconnectTxs, hw]
              exact ⟨w, rfl, hwe⟩

private theorem equiv_refl (u : Ledger) : BitcoinBlockV2.Equiv u u := fun _ => rfl

private theorem equiv_symm {u v : Ledger} (h : BitcoinBlockV2.Equiv u v) : BitcoinBlockV2.Equiv v u := fun op => (h op).symm

private theorem equiv_trans {u v w : Ledger} (h1 : BitcoinBlockV2.Equiv u v) (h2 : BitcoinBlockV2.Equiv v w) :
    BitcoinBlockV2.Equiv u w := fun op => (h1 op).trans (h2 op)

private theorem accessCoin_equiv {u v : Ledger} (h : BitcoinBlockV2.Equiv u v) (op : BitcoinSer.OutPoint) :
    BitcoinBlockV2.accessCoin u op = BitcoinBlockV2.accessCoin v op := by
  simp only [accessCoin, h op]

private theorem haveCoin_equiv {u v : Ledger} (h : BitcoinBlockV2.Equiv u v) (op : BitcoinSer.OutPoint) :
    BitcoinBlockV2.haveCoin u op = BitcoinBlockV2.haveCoin v op := by
  simp only [haveCoin, h op]

private theorem inputsLoop_equiv {u v : Ledger} (h : BitcoinBlockV2.Equiv u v) (H : Nat) :
    ∀ (ins : List BitcoinSer.TxIn) (acc : Int), BitcoinBlockV2.inputsLoop u H ins acc = BitcoinBlockV2.inputsLoop v H ins acc
  | [], acc => rfl
  | i :: rest, acc => by
    simp only [inputsLoop, h i.prevout]
    cases getCoin v i.prevout with
    | none => rfl
    | some c =>
      simp only
      split
      · rfl
      · split
        · rfl
        · exact inputsLoop_equiv h H rest _

private theorem valueIn_equiv {u v : Ledger} (h : BitcoinBlockV2.Equiv u v) :
    ∀ (ins : List BitcoinSer.TxIn), BitcoinBlockV2.valueIn u ins = BitcoinBlockV2.valueIn v ins
  | [] => rfl
  | i :: rest => by simp only [valueIn, accessCoin_equiv h, valueIn_equiv h rest]

private theorem checkTxInputs_equiv {u v : Ledger} (h : BitcoinBlockV2.Equiv u v) (tx : BitcoinSer.Tx) (H : Nat) :
    BitcoinBlockV2.checkTxInputs u tx H = BitcoinBlockV2.checkTxInputs v tx H := by
  simp only [checkTxInputs, inputsLoop_equiv h]
  have : (tx.vin.all fun i => haveCoin u i.prevout) = (tx.vin.all fun i => haveCoin v i.prevout) := by
    congr 1; funext i; exact haveCoin_equiv h _
  rw [this]

private theorem sequenceLocksOk_equiv {u v : Ledger} (h : BitcoinBlockV2.Equiv u v) (H : Nat) (mtp : Nat → Nat)
    (ltf : Nat) (tx : BitcoinSer.Tx) :
    BitcoinBlockV2.sequenceLocksOk u H mtp ltf tx = BitcoinBlockV2.sequenceLocksOk v H mtp ltf tx := by
  simp only [sequenceLocksOk, accessCoin_equiv h]

private theorem txSigOpCost_equiv {u v : Ledger} (h : BitcoinBlockV2.Equiv u v) (f : BitcoinActivation.ScriptFlags)
    (tx : BitcoinSer.Tx) : BitcoinBlockV2.txSigOpCost f u tx = BitcoinBlockV2.txSigOpCost f v tx := by
  simp only [txSigOpCost, accessCoin_equiv h]

private theorem inputScriptsOk_equiv {u v : Ledger} (h : BitcoinBlockV2.Equiv u v) (f : BitcoinActivation.ScriptFlags)
    (tx : BitcoinSer.Tx) : BitcoinBlockV2.inputScriptsOk f u tx = BitcoinBlockV2.inputScriptsOk f v tx := by
  simp only [inputScriptsOk, accessCoin_equiv h]

private theorem txUndo_equiv {u v : Ledger} (h : BitcoinBlockV2.Equiv u v) (tx : BitcoinSer.Tx) :
    BitcoinBlockV2.txUndo u tx = BitcoinBlockV2.txUndo v tx := by
  simp only [txUndo, accessCoin_equiv h]

/-- The loop's outcome on equivalent ledgers: both fail, or both succeed with equivalent ledgers
and the same fees, sigop count and undo data. -/
private theorem connectLoop_equiv (f : BitcoinActivation.ScriptFlags) (H : Nat) (mtp : Nat → Nat) (ltf : Nat) :
    ∀ (txs : List BitcoinSer.Tx) (u v : Ledger) (fees : Int) (sig : Nat) (undo : BlockUndo), BitcoinBlockV2.Equiv u v →
    (BitcoinBlockV2.connectLoop f H mtp ltf ⟨u, fees, sig, undo⟩ txs = none ∧
       BitcoinBlockV2.connectLoop f H mtp ltf ⟨v, fees, sig, undo⟩ txs = none) ∨
    (∃ a b, BitcoinBlockV2.connectLoop f H mtp ltf ⟨u, fees, sig, undo⟩ txs = some a ∧
       BitcoinBlockV2.connectLoop f H mtp ltf ⟨v, fees, sig, undo⟩ txs = some b ∧
       BitcoinBlockV2.Equiv a.utxo b.utxo ∧ a.fees = b.fees ∧ a.sigOps = b.sigOps ∧ a.undo = b.undo)
  | [], u, v, fees, sig, undo, h => Or.inr ⟨_, _, rfl, rfl, h, rfl, rfl, rfl⟩
  | tx :: rest, u, v, fees, sig, undo, h => by
    simp only [connectLoop, checkTxInputs_equiv h, sequenceLocksOk_equiv h, txSigOpCost_equiv h,
      inputScriptsOk_equiv h, txUndo_equiv h]
    -- the step decisions are now literally the same expression on both sides
    split
    · exact Or.inl ⟨rfl, rfl⟩
    · split
      · exact Or.inl ⟨rfl, rfl⟩
      · split
        · exact Or.inl ⟨rfl, rfl⟩
        · exact connectLoop_equiv f H mtp ltf rest _ _ _ _ _ (BitcoinReorg.updateCoins_equiv u v h tx H)

private theorem bip30Ok_equiv {u v : Ledger} (h : BitcoinBlockV2.Equiv u v) (b : BitcoinSer.Block) :
    BitcoinBlockV2.bip30Ok u b = BitcoinBlockV2.bip30Ok v b := by
  simp only [bip30Ok, haveCoin_equiv h]

/-- The header path does not read the ledger. -/
private def relabel (T : ChainState) : Outcome → Outcome
  | .accept _ _ => .accept T []
  | .invalid => .invalid
  | .futureTime => .futureTime
  | .missingPrev => .missingPrev

private theorem acceptHeader_ledger (H : List BitcoinSer.Header) (u v : Ledger) (hd : BitcoinSer.Header) (now : Int) :
    BitcoinBlockV2.acceptHeader ⟨H, v⟩ hd now = relabel ⟨H, v⟩ (BitcoinBlockV2.acceptHeader ⟨H, u⟩ hd now) := by
  have e1 : (⟨H, v⟩ : ChainState).tipHash = (⟨H, u⟩ : ChainState).tipHash := rfl
  have e2 : (⟨H, v⟩ : ChainState).requiredBits = (⟨H, u⟩ : ChainState).requiredBits := rfl
  have e3 : (⟨H, v⟩ : ChainState).mtp = (⟨H, u⟩ : ChainState).mtp := rfl
  have e4 : (⟨H, v⟩ : ChainState).tipHeight = (⟨H, u⟩ : ChainState).tipHeight := rfl
  simp only [acceptHeader, e1, e2, e3, e4]
  repeat' split
  all_goals rfl

private theorem stateEquiv_refl (S : ChainState) : BitcoinReorg.StateEquiv S S := ⟨rfl, equiv_refl _⟩

private theorem stateEquiv_symm {S T : ChainState} (h : BitcoinReorg.StateEquiv S T) : BitcoinReorg.StateEquiv T S :=
  ⟨h.1.symm, equiv_symm h.2⟩

private theorem stateEquiv_trans {S T U : ChainState} (h1 : BitcoinReorg.StateEquiv S T) (h2 : BitcoinReorg.StateEquiv T U) :
    BitcoinReorg.StateEquiv S U := ⟨h1.1.trans h2.1, equiv_trans h1.2 h2.2⟩

/-- Every state along a chain connected to a reachable state is reachable. -/
theorem solution (S : ChainState) (hR : BitcoinBlockV2.Reachable S) :
    ∀ (bs : List (BitcoinSer.Block × Int)) (T : ChainState) (undos : List BlockUndo),
    BitcoinReorg.connectChain S bs = some (T, undos) → BitcoinBlockV2.Reachable T := by
  intro bs
  induction bs generalizing S with
  | nil => intro T undos h; simp only [connectChain, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact hR
  | cons p rest ih =>
    intro T undos h
    obtain ⟨b, now⟩ := p
    simp only [connectChain] at h
    cases hv : validate S b now with
    | accept S' undo =>
      rw [hv] at h; dsimp only at h
      cases hc : connectChain S' rest with
      | none => rw [hc] at h; cases h
      | some q =>
        rw [hc] at h
        obtain ⟨T', undos'⟩ := q
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        exact ih S' (Reachable.step hR hv) T' undos' hc
    | invalid => rw [hv] at h; cases h
    | futureTime => rw [hv] at h; cases h
    | missingPrev => rw [hv] at h; cases h

-- Prove2me | solution 1 for BitcoinUtxo.block_bound
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:08.886255+00:00
-- url     : https://prove2.me/submissions/6322ddea-5003-4eae-8da5-df7142114f94

import Definitions.Def_BitcoinUtxo
import Theorems.Thm_BitcoinUtxo_checkTransaction_outputs
import Theorems.Thm_BitcoinUtxo_tx_conservation
import Theorems.Thm_BitcoinUtxo_coinbase_bound

open BitcoinUtxo

private theorem getCoin_cons {T : Type} [DecidableEq T] (k : OutPoint T) (c : Coin) (rest : UtxoSet T) (op : OutPoint T) :
    getCoin ((k, c) :: rest) op = if k = op then some c else getCoin rest op := rfl

private theorem keysNodup_cons {T : Type} [DecidableEq T] (k : OutPoint T) (c : Coin) (rest : UtxoSet T) :
    keysNodup ((k, c) :: rest) ↔ (∀ e ∈ rest, e.1 ≠ k) ∧ keysNodup rest := by
  unfold keysNodup
  simp only [List.map_cons, List.nodup_cons, List.mem_map]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun e he hek => h1 ⟨e, he, hek⟩, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun ⟨e, he, hek⟩ => h1 e he hek, h2⟩

private theorem getCoin_spend_self {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) :
    getCoin (spendCoin u op) op = none := by
  induction u with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, c⟩ := e
    unfold spendCoin
    by_cases hk : k = op
    · rw [if_pos hk]; exact ih
    · rw [if_neg hk]; unfold getCoin; rw [if_neg hk]; exact ih

private theorem getCoin_spend_other {T : Type} [DecidableEq T] (u : UtxoSet T) (op op' : OutPoint T) (h : op' ≠ op) :
    getCoin (spendCoin u op) op' = getCoin u op' := by
  induction u with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, c⟩ := e
    unfold spendCoin
    by_cases hk : k = op
    · rw [if_pos hk]
      rw [getCoin_cons]
      have : ¬ k = op' := fun h' => h (h'.symm.trans hk)
      rw [if_neg this]; exact ih
    · rw [if_neg hk]
      rw [getCoin_cons, getCoin_cons]
      by_cases hk' : k = op'
      · rw [if_pos hk', if_pos hk']
      · rw [if_neg hk', if_neg hk']; exact ih

private theorem mem_spendCoin {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) (e : OutPoint T × Coin)
    (h : e ∈ spendCoin u op) : e ∈ u := by
  induction u with
  | nil => simp [spendCoin] at h
  | cons f rest ih =>
    obtain ⟨k, c⟩ := f
    unfold spendCoin at h
    by_cases hk : k = op
    · rw [if_pos hk] at h; exact List.mem_cons_of_mem _ (ih h)
    · rw [if_neg hk] at h
      rcases List.mem_cons.1 h with rfl | hm
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hm)

private theorem keysNodup_spend {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) (h : keysNodup u) :
    keysNodup (spendCoin u op) := by
  induction u with
  | nil => exact h
  | cons e rest ih =>
    obtain ⟨k, c⟩ := e
    obtain ⟨hkeys, hrest⟩ := (keysNodup_cons k c rest).1 h
    unfold spendCoin
    by_cases hk : k = op
    · rw [if_pos hk]; exact ih hrest
    · rw [if_neg hk]
      apply (keysNodup_cons k c _).2
      exact ⟨fun e he => hkeys e (mem_spendCoin rest op e he), ih hrest⟩

private theorem getCoin_add_other {T : Type} [DecidableEq T] (u : UtxoSet T) (op op' : OutPoint T) (c : Coin) (h : op' ≠ op) :
    getCoin (addCoin u op c) op' = getCoin u op' := by
  unfold addCoin
  split
  · rfl
  · rw [getCoin_cons, if_neg (Ne.symm h)]
    exact getCoin_spend_other u op op' h

private theorem keysNodup_add {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) (c : Coin) (h : keysNodup u) :
    keysNodup (addCoin u op c) := by
  unfold addCoin
  split
  · exact h
  · apply (keysNodup_cons op c _).2
    refine ⟨?_, keysNodup_spend u op h⟩
    intro e he heq
    have : getCoin (spendCoin u op) op = none := getCoin_spend_self u op
    -- e is in the spent set with key op, contradicting the lookup
    have hmem : e.1 = op := heq
    have key : ∀ (v : UtxoSet T) (e : OutPoint T × Coin), e ∈ v → getCoin v e.1 ≠ none := by
      intro v e hev
      induction v with
      | nil => simp at hev
      | cons f rest ih =>
        unfold getCoin
        by_cases hf : f.1 = e.1
        · obtain ⟨fk, fc⟩ := f; simp only at hf; rw [if_pos hf]; simp
        · obtain ⟨fk, fc⟩ := f; simp only at hf; rw [if_neg hf]
          rcases List.mem_cons.1 hev with rfl | hm
          · exact absurd rfl hf
          · exact ih hm
    exact key _ e he (hmem ▸ this)

private theorem haveCoin_false_iff {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) :
    haveCoin u op = false ↔ getCoin u op = none := by
  unfold haveCoin
  cases getCoin u op <;> simp

private theorem getCoin_spendInputs_none {T : Type} [DecidableEq T] (u : UtxoSet T) :
    ∀ (ops : List (OutPoint T)) (op : OutPoint T), getCoin u op = none → getCoin (spendInputs u ops) op = none
  | [], op, h => h
  | op' :: rest, op, h => by
    unfold spendInputs
    apply getCoin_spendInputs_none (spendCoin u op') rest op
    by_cases hop : op = op'
    · subst hop; exact getCoin_spend_self u op
    · rw [getCoin_spend_other u op' op hop]; exact h

private theorem keysNodup_spendInputs {T : Type} [DecidableEq T] (u : UtxoSet T) :
    ∀ (ops : List (OutPoint T)), keysNodup u → keysNodup (spendInputs u ops)
  | [], h => h
  | op :: rest, h => by
    unfold spendInputs
    exact keysNodup_spendInputs (spendCoin u op) rest (keysNodup_spend u op h)

private theorem getCoin_addCoinsFrom_other {T : Type} [DecidableEq T] (txid : T) (h : Nat) (cb : Bool) :
    ∀ (outs : List TxOut) (u : UtxoSet T) (i : Nat) (op : OutPoint T), op.txid ≠ txid →
      getCoin (addCoinsFrom txid h cb u i outs) op = getCoin u op
  | [], u, i, op, _ => rfl
  | o :: rest, u, i, op, hne => by
    unfold addCoinsFrom
    rw [getCoin_addCoinsFrom_other txid h cb rest _ (i + 1) op hne]
    apply getCoin_add_other
    intro e; cases e; exact hne rfl

private theorem keysNodup_addCoinsFrom {T : Type} [DecidableEq T] (txid : T) (h : Nat) (cb : Bool) :
    ∀ (outs : List TxOut) (u : UtxoSet T) (i : Nat), keysNodup u → keysNodup (addCoinsFrom txid h cb u i outs)
  | [], u, i, hn => hn
  | o :: rest, u, i, hn => by
    unfold addCoinsFrom
    exact keysNodup_addCoinsFrom txid h cb rest _ (i + 1) (keysNodup_add u _ _ hn)

private theorem getCoin_updateCoins_other {T : Type} [DecidableEq T] (u : UtxoSet T) (tx : Tx T) (h : Nat) (op : OutPoint T)
    (hne : op.txid ≠ tx.txid) (hnone : getCoin u op = none) :
    getCoin (updateCoins u tx h) op = none := by
  unfold updateCoins
  rw [getCoin_addCoinsFrom_other tx.txid h tx.isCoinbase tx.vout _ 0 op hne]
  split
  · exact hnone
  · exact getCoin_spendInputs_none u tx.vin op hnone

private theorem keysNodup_updateCoins {T : Type} [DecidableEq T] (u : UtxoSet T) (tx : Tx T) (h : Nat) (hn : keysNodup u) :
    keysNodup (updateCoins u tx h) := by
  unfold updateCoins
  apply keysNodup_addCoinsFrom
  split
  · exact hn
  · exact keysNodup_spendInputs u tx.vin hn

/-- Sum of the output values of the coinbase transactions of a list. -/
private def cbOut {T : Type} [DecidableEq T] : List (Tx T) → Int
  | [] => 0
  | tx :: rest => (if tx.isCoinbase then valueOut tx else 0) + cbOut rest

private theorem cbOut_of_no_coinbase {T : Type} [DecidableEq T] : ∀ (txs : List (Tx T)), (∀ tx ∈ txs, tx.isCoinbase = false) → cbOut txs = 0
  | [], _ => rfl
  | tx :: rest, h => by
    unfold cbOut
    rw [h tx (List.mem_cons_self ..)]
    simp only [Bool.false_eq_true, ite_false, Int.zero_add]
    exact cbOut_of_no_coinbase rest (fun tx' h' => h tx' (List.mem_cons_of_mem _ h'))

private theorem connectLoop_bound {T : Type} [DecidableEq T] (h : Nat) :
    ∀ (txs : List (Tx T)) (u : UtxoSet T) (fees : Int) (u' : UtxoSet T) (fees' : Int),
      keysNodup u → (∀ tx ∈ txs, checkTransaction tx = true) →
      (∀ tx ∈ txs, ∀ j, j < tx.vout.length → getCoin u ⟨tx.txid, j⟩ = none) →
      (txs.map Tx.txid).Nodup →
      connectLoop h u fees txs = some (u', fees') →
      totalValue u' + fees' ≤ totalValue u + fees + cbOut txs ∧ keysNodup u'
  | [], u, fees, u', fees', hn, _, _, _, hc => by
    simp only [connectLoop, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨by unfold cbOut; omega, hn⟩
  | tx :: rest, u, fees, u', fees', hn, hchk, hfresh, hnd, hc => by
    unfold connectLoop at hc
    have hchk_tx := hchk tx (List.mem_cons_self ..)
    obtain ⟨hnd_in, hpos⟩ := BitcoinUtxo.checkTransaction_outputs tx hchk_tx
    have hpos' : ∀ o ∈ tx.vout, 0 ≤ o.value := fun o ho => (hpos o ho).1
    have hfresh_tx := hfresh tx (List.mem_cons_self ..)
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hnotin, hnd_rest⟩ := hnd
    have hfresh_rest : ∀ tx' ∈ rest, ∀ j, j < tx'.vout.length →
        getCoin (updateCoins u tx h) ⟨tx'.txid, j⟩ = none := by
      intro tx' htx' j hj
      apply getCoin_updateCoins_other
      · intro e; exact hnotin ⟨tx', htx', e⟩
      · exact hfresh tx' (List.mem_cons_of_mem _ htx') j hj
    have hn' := keysNodup_updateCoins u tx h hn
    have hchk_rest : ∀ tx' ∈ rest, checkTransaction tx' = true :=
      fun tx' h' => hchk tx' (List.mem_cons_of_mem _ h')
    split at hc
    · rename_i hcb
      obtain ⟨ih1, ih2⟩ := connectLoop_bound h rest _ fees u' fees' hn' hchk_rest hfresh_rest hnd_rest hc
      have hb := BitcoinUtxo.coinbase_bound u tx h hcb hfresh_tx hpos'
      unfold cbOut; rw [if_pos hcb]
      exact ⟨by omega, ih2⟩
    · rename_i hcb
      have hcb' : tx.isCoinbase = false := by
        cases e : tx.isCoinbase
        · rfl
        · exact absurd e hcb
      cases hf : checkTxInputs u tx h with
      | none => rw [hf] at hc; simp at hc
      | some fee =>
        rw [hf] at hc
        simp only [] at hc
        split at hc
        · simp at hc
        · obtain ⟨ih1, ih2⟩ := connectLoop_bound h rest _ (fees + fee) u' fees' hn' hchk_rest hfresh_rest hnd_rest hc
          have ht := BitcoinUtxo.tx_conservation u tx h fee hn hnd_in hcb' hf hfresh_tx hpos'
          unfold cbOut; rw [if_neg hcb]
          exact ⟨by omega, ih2⟩

/-- Connecting a block raises the ledger's total value by at most the block subsidy, and keeps
the outpoints distinct. -/
theorem solution {T : Type} [DecidableEq T] (subsidy : Nat → Int) (u : UtxoSet T) (h : Nat) (block : List (Tx T))
    (u' : UtxoSet T) (fees : Int) (hn : keysNodup u) (hnd : (block.map Tx.txid).Nodup)
    (hc : connectBlock subsidy u h block = some (u', fees)) :
    totalValue u' ≤ totalValue u + subsidy h ∧ keysNodup u' := by
  unfold connectBlock at hc
  split at hc
  · simp at hc
  rename_i hchk
  split at hc
  · simp at hc
  rename_i hbip
  have hchk' : checkBlockTxs block = true := by
    cases e : checkBlockTxs block
    · rw [e] at hchk; simp at hchk
    · rfl
  have hbip' : bip30Ok u block = true := by
    cases e : bip30Ok u block
    · rw [e] at hbip; simp at hbip
    · rfl
  cases hl : connectLoop h u 0 block with
  | none => rw [hl] at hc; simp at hc
  | some p =>
    obtain ⟨u1, fees1⟩ := p
    rw [hl] at hc
    cases block with
    | nil => simp [checkBlockTxs] at hchk'
    | cons cb rest =>
      simp only [] at hc
      split at hc
      · simp at hc
      rename_i hreward
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      -- structural facts
      unfold checkBlockTxs at hchk'
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hchk'
      obtain ⟨⟨hcbcb, hcbchk⟩, hrest⟩ := hchk'
      have hall_chk : ∀ tx ∈ cb :: rest, checkTransaction tx = true := by
        intro tx htx
        rcases List.mem_cons.1 htx with rfl | hm
        · exact hcbchk
        · exact (hrest tx hm).2
      have hno_cb : ∀ tx ∈ rest, tx.isCoinbase = false := fun tx hm => (hrest tx hm).1
      -- BIP30 freshness
      unfold bip30Ok at hbip'
      simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true'] at hbip'
      have hfresh : ∀ tx ∈ cb :: rest, ∀ j, j < tx.vout.length → getCoin u ⟨tx.txid, j⟩ = none :=
        fun tx htx j hj => (haveCoin_false_iff u _).1 (hbip' tx htx j hj)
      obtain ⟨hb1, hb2⟩ := connectLoop_bound h (cb :: rest) u 0 _ _ hn hall_chk hfresh hnd hl
      have hcb0 : cbOut (cb :: rest) = valueOut cb := by
        unfold cbOut; rw [if_pos hcbcb, cbOut_of_no_coinbase rest hno_cb]; omega
      rw [hcb0] at hb1
      simp only [gt_iff_lt, Int.not_lt] at hreward
      exact ⟨by omega, hb2⟩

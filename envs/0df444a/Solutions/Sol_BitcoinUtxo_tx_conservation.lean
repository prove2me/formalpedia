-- Prove2me | solution 1 for BitcoinUtxo.tx_conservation
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:07.610007+00:00
-- url     : https://prove2.me/submissions/350bf03b-78a7-4f66-b4a9-4a6bf8e577bf

import Definitions.Def_BitcoinUtxo
import Theorems.Thm_BitcoinUtxo_totalValue_add_fresh
import Theorems.Thm_BitcoinUtxo_totalValue_spendInputs
import Theorems.Thm_BitcoinUtxo_checkTxInputs_some

open BitcoinUtxo

private theorem getCoin_cons {T : Type} [DecidableEq T] (k : OutPoint T) (c : Coin) (rest : UtxoSet T) (op : OutPoint T) :
    getCoin ((k, c) :: rest) op = if k = op then some c else getCoin rest op := rfl

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

private theorem getCoin_add_other {T : Type} [DecidableEq T] (u : UtxoSet T) (op op' : OutPoint T) (c : Coin) (h : op' ≠ op) :
    getCoin (addCoin u op c) op' = getCoin u op' := by
  unfold addCoin
  split
  · rfl
  · rw [getCoin_cons, if_neg (Ne.symm h)]
    exact getCoin_spend_other u op op' h

private theorem getCoin_spendInputs_none {T : Type} [DecidableEq T] (u : UtxoSet T) :
    ∀ (ops : List (OutPoint T)) (op : OutPoint T), getCoin u op = none → getCoin (spendInputs u ops) op = none
  | [], op, h => h
  | op' :: rest, op, h => by
    unfold spendInputs
    apply getCoin_spendInputs_none (spendCoin u op') rest op
    by_cases hop : op = op'
    · subst hop; exact getCoin_spend_self u op
    · rw [getCoin_spend_other u op' op hop]; exact h

private theorem outpoint_ne_of_ne_n {T : Type} [DecidableEq T] (txid : T) (i j : Nat) (h : j ≠ i) :
    (⟨txid, j⟩ : OutPoint T) ≠ ⟨txid, i⟩ := by
  intro e; cases e; exact h rfl

private theorem totalValue_addCoinsFrom {T : Type} [DecidableEq T] (txid : T) (h : Nat) (cb : Bool) :
    ∀ (outs : List TxOut) (u : UtxoSet T) (i : Nat),
      (∀ j, i ≤ j → j < i + outs.length → getCoin u ⟨txid, j⟩ = none) →
      (∀ o ∈ outs, 0 ≤ o.value) →
      totalValue (addCoinsFrom txid h cb u i outs) ≤ totalValue u + sumValues outs
  | [], u, i, _, _ => by simp [addCoinsFrom, sumValues]
  | o :: rest, u, i, hfresh, hpos => by
    unfold addCoinsFrom
    have hfi : getCoin u ⟨txid, i⟩ = none := hfresh i (Nat.le_refl _) (by simp)
    have hadd := BitcoinUtxo.totalValue_add_fresh u ⟨txid, i⟩ ⟨o, h, cb⟩ hfi
    have hfresh' : ∀ j, i + 1 ≤ j → j < i + 1 + rest.length → getCoin (addCoin u ⟨txid, i⟩ ⟨o, h, cb⟩) ⟨txid, j⟩ = none := by
      intro j hj1 hj2
      rw [getCoin_add_other u _ _ _ (outpoint_ne_of_ne_n txid i j (by omega))]
      exact hfresh j (by omega) (by simp; omega)
    have ih := totalValue_addCoinsFrom txid h cb rest _ (i + 1) hfresh'
      (fun o' ho' => hpos o' (List.mem_cons_of_mem _ ho'))
    have ho : 0 ≤ o.value := hpos o (List.mem_cons_self ..)
    unfold sumValues
    simp only at hadd
    split at hadd <;> omega

/-- An accepted ordinary transaction removes exactly its fee from the ledger, or more when it
has unspendable outputs: it cannot create value. -/
theorem solution {T : Type} [DecidableEq T] (u : UtxoSet T) (tx : Tx T) (h : Nat) (fee : Int)
    (hn : keysNodup u) (hnd : tx.vin.Nodup) (hcb : tx.isCoinbase = false)
    (hfee : checkTxInputs u tx h = some fee)
    (hfresh : ∀ j, j < tx.vout.length → getCoin u ⟨tx.txid, j⟩ = none)
    (hpos : ∀ o ∈ tx.vout, 0 ≤ o.value) :
    totalValue (updateCoins u tx h) ≤ totalValue u - fee := by
  obtain ⟨hfeeq, -, -, hall⟩ := BitcoinUtxo.checkTxInputs_some u tx h fee hfee
  unfold updateCoins
  rw [hcb]
  simp only [Bool.false_eq_true, ite_false]
  have hsp := BitcoinUtxo.totalValue_spendInputs u tx.vin hn hnd hall
  have hfresh' : ∀ j, 0 ≤ j → j < 0 + tx.vout.length → getCoin (spendInputs u tx.vin) ⟨tx.txid, j⟩ = none :=
    fun j _ hj => getCoin_spendInputs_none u tx.vin _ (hfresh j (by omega))
  have hadd := totalValue_addCoinsFrom tx.txid h false tx.vout (spendInputs u tx.vin) 0 hfresh' hpos
  unfold valueOut at hfeeq
  omega

-- Prove2me | solution 1 for BitcoinReorg.updateCoins_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T02:08:48.093976+00:00
-- url     : https://prove2.me/submissions/0bc4397b-3ff3-4bb9-91c0-d41c896051ef

import Definitions.Def_BitcoinReorg
import Definitions.Def_BitcoinSer
open BitcoinReorg BitcoinBlockV2

namespace BtcAux
open BitcoinSer

theorem getCoin_spendCoin (u : Ledger) (op q : OutPoint) :
    getCoin (spendCoin u op) q = if q = op then none else getCoin u q := by
  induction u with
  | nil => simp [spendCoin, getCoin]
  | cons p rest ih =>
    obtain ⟨k, c⟩ := p
    by_cases hk : k = op
    · subst hk
      by_cases hq : q = k
      · subst hq; simp [spendCoin, ih]
      · have : ¬ k = q := fun h => hq h.symm
        simp [spendCoin, getCoin, ih, hq, this]
    · by_cases hq : q = op
      · subst hq
        have : ¬ k = q := hk
        simp [spendCoin, getCoin, ih, hk, this]
      · simp only [spendCoin, hk, if_false, getCoin, ih, hq]

theorem equiv_spendCoin {u v : Ledger} (h : Equiv u v) (op : OutPoint) :
    Equiv (spendCoin u op) (spendCoin v op) := by
  intro q; rw [getCoin_spendCoin, getCoin_spendCoin, h q]

theorem getCoin_addCoin (u : Ledger) (op : OutPoint) (c : Coin) (q : OutPoint) :
    getCoin (addCoin u op c) q =
      if isUnspendable c.out.scriptPubKey then getCoin u q
      else if q = op then some c else getCoin (spendCoin u op) q := by
  unfold addCoin
  by_cases hu : isUnspendable c.out.scriptPubKey
  · simp [hu]
  · by_cases hq : q = op
    · subst hq; simp [hu, getCoin]
    · have : ¬ op = q := fun h => hq h.symm
      simp [hu, getCoin, hq, this]

theorem equiv_addCoin {u v : Ledger} (h : Equiv u v) (op : OutPoint) (c : Coin) :
    Equiv (addCoin u op c) (addCoin v op c) := by
  intro q
  rw [getCoin_addCoin, getCoin_addCoin, h q, equiv_spendCoin h op q]

theorem equiv_addCoinsFrom (txid : Bytes) (height : Nat) (cb : Bool) (outs : List TxOut) :
    ∀ (u v : Ledger) (i : Nat), Equiv u v →
      Equiv (addCoinsFrom txid height cb u i outs) (addCoinsFrom txid height cb v i outs) := by
  induction outs with
  | nil => intro u v i h; simpa [addCoinsFrom] using h
  | cons o rest ih =>
    intro u v i h
    simp only [addCoinsFrom]
    exact ih _ _ _ (equiv_addCoin h _ _)

theorem equiv_spendInputs (ins : List TxIn) :
    ∀ (u v : Ledger), Equiv u v → Equiv (spendInputs u ins) (spendInputs v ins) := by
  induction ins with
  | nil => intro u v h; simpa [spendInputs] using h
  | cons i rest ih =>
    intro u v h
    simp only [spendInputs]
    exact ih _ _ (equiv_spendCoin h _)

theorem equiv_updateCoins {u v : Ledger} (h : Equiv u v) (tx : Tx) (H : Nat) :
    Equiv (updateCoins u tx H) (updateCoins v tx H) := by
  unfold updateCoins
  apply equiv_addCoinsFrom
  by_cases hc : isCoinBase tx = true
  · rw [if_pos hc, if_pos hc]; exact h
  · rw [if_neg hc, if_neg hc]; exact equiv_spendInputs _ _ _ h

end BtcAux

theorem solution (u v : Ledger) (h : BitcoinBlockV2.Equiv u v) (tx : BitcoinSer.Tx) (H : Nat) :
    BitcoinBlockV2.Equiv (BitcoinBlockV2.updateCoins u tx H) (BitcoinBlockV2.updateCoins v tx H) :=
  BtcAux.equiv_updateCoins h tx H

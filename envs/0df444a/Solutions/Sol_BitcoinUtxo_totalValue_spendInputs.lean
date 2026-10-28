-- Prove2me | solution 1 for BitcoinUtxo.totalValue_spendInputs
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:07.012513+00:00
-- url     : https://prove2.me/submissions/14d9d8ca-d6e5-4c5a-a52b-f91eb80a2a04

import Definitions.Def_BitcoinUtxo
import Theorems.Thm_BitcoinUtxo_totalValue_spend

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

private theorem haveCoin_true_iff {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) :
    haveCoin u op = true ↔ ∃ c, getCoin u op = some c := by
  unfold haveCoin
  cases getCoin u op <;> simp

private theorem valueIn_spend_of_not_mem {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) :
    ∀ (ops : List (OutPoint T)), op ∉ ops → valueIn (spendCoin u op) ops = valueIn u ops
  | [], _ => rfl
  | op' :: rest, h => by
    simp only [List.mem_cons, not_or] at h
    unfold valueIn
    rw [getCoin_spend_other u op op' (fun e => h.1 e.symm),
      valueIn_spend_of_not_mem u op rest h.2]

theorem solution {T : Type} [DecidableEq T] (u : UtxoSet T) :
    ∀ (ops : List (OutPoint T)), keysNodup u → ops.Nodup → (∀ op ∈ ops, haveCoin u op = true) →
      totalValue (spendInputs u ops) = totalValue u - valueIn u ops
  | [], _, _, _ => by simp [spendInputs, valueIn]
  | op :: rest, hn, hnd, hall => by
    unfold spendInputs valueIn
    obtain ⟨c, hc⟩ := (haveCoin_true_iff u op).1 (hall op (List.mem_cons_self ..))
    rw [hc]
    dsimp only
    simp only [List.nodup_cons] at hnd
    have hrest : ∀ op' ∈ rest, haveCoin (spendCoin u op) op' = true := by
      intro op' hop'
      have hne : op' ≠ op := fun h => hnd.1 (h ▸ hop')
      unfold haveCoin
      rw [getCoin_spend_other u op op' hne]
      exact hall op' (List.mem_cons_of_mem _ hop')
    rw [solution (spendCoin u op) rest (keysNodup_spend u op hn) hnd.2 hrest,
      BitcoinUtxo.totalValue_spend u op c hn hc, valueIn_spend_of_not_mem u op rest hnd.1]
    omega

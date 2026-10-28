-- Prove2me | solution 1 for BitcoinUtxo.totalValue_spend
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:05.7881+00:00
-- url     : https://prove2.me/submissions/7b1f6d04-bf6d-4eb6-a48e-75aab1e7efc2

import Definitions.Def_BitcoinUtxo

open BitcoinUtxo

private theorem totalValue_cons {T : Type} [DecidableEq T] (k : OutPoint T) (c : Coin) (rest : UtxoSet T) :
    totalValue ((k, c) :: rest) = c.out.value + totalValue rest := rfl

private theorem keysNodup_cons {T : Type} [DecidableEq T] (k : OutPoint T) (c : Coin) (rest : UtxoSet T) :
    keysNodup ((k, c) :: rest) ↔ (∀ e ∈ rest, e.1 ≠ k) ∧ keysNodup rest := by
  unfold keysNodup
  simp only [List.map_cons, List.nodup_cons, List.mem_map]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun e he hek => h1 ⟨e, he, hek⟩, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun ⟨e, he, hek⟩ => h1 e he hek, h2⟩

private theorem getCoin_none_of_keys {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T)
    (h : ∀ e ∈ u, e.1 ≠ op) : getCoin u op = none := by
  induction u with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, c⟩ := e
    unfold getCoin
    have hk : ¬ k = op := h (k, c) (List.mem_cons_self ..)
    rw [if_neg hk]
    exact ih (fun e he => h e (List.mem_cons_of_mem _ he))

private theorem spendCoin_of_none {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) (h : getCoin u op = none) :
    spendCoin u op = u := by
  induction u with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, c⟩ := e
    unfold getCoin at h
    by_cases hk : k = op
    · rw [if_pos hk] at h; simp at h
    · rw [if_neg hk] at h
      unfold spendCoin
      rw [if_neg hk, ih h]

theorem solution {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) (c : Coin)
    (hn : keysNodup u) (h : getCoin u op = some c) :
    totalValue (spendCoin u op) = totalValue u - c.out.value := by
  induction u with
  | nil => simp [getCoin] at h
  | cons e rest ih =>
    obtain ⟨k, c'⟩ := e
    obtain ⟨hkeys, hrest⟩ := (keysNodup_cons k c' rest).1 hn
    unfold getCoin at h
    unfold spendCoin
    by_cases hk : k = op
    · rw [if_pos hk] at h
      rw [if_pos hk]
      simp only [Option.some.injEq] at h
      subst h
      have hnone : getCoin rest op = none := getCoin_none_of_keys rest op (fun e he => hk ▸ hkeys e he)
      rw [spendCoin_of_none rest op hnone, totalValue_cons]; omega
    · rw [if_neg hk] at h
      rw [if_neg hk, totalValue_cons, totalValue_cons]
      have := ih hrest h
      omega

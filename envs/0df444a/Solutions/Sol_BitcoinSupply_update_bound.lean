-- Prove2me | solution 1 for BitcoinSupply.update_bound
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T00:04:17.854222+00:00
-- url     : https://prove2.me/submissions/f54ff320-f38e-4669-8f89-34335a404f42

import Definitions.Def_BitcoinSupply
import Theorems.Thm_BitcoinBlockV2_acceptance
import Theorems.Thm_BitcoinBlockV2_apply_spec
import Theorems.Thm_BitcoinBlockV2_reachable_wellFormed
import Theorems.Thm_BitcoinSubsidy_issuance_bound
import Theorems.Thm_BitcoinSubsidy_core_eq_spec

open BitcoinSupply BitcoinBlockV2

private theorem totalValue_cons (e : BitcoinSer.OutPoint × Coin) (u : Ledger) :
    totalValue (e :: u) = e.2.out.nValue + totalValue u := rfl

/-- `spendCoin` on a ledger with distinct keys removes exactly the coin at `op`, if any. -/
private theorem totalValue_spendCoin : ∀ (u : Ledger) (op : BitcoinSer.OutPoint), keysNodup u →
    totalValue (spendCoin u op) = totalValue u - (match getCoin u op with | some c => c.out.nValue | none => 0)
  | [], op, _ => by simp [spendCoin, getCoin, totalValue]
  | (k, c) :: rest, op, hnd => by
    have hnd' : keysNodup rest := by
      simp only [keysNodup, List.map_cons, List.nodup_cons] at hnd; exact hnd.2
    have hk : k ∉ rest.map Prod.fst := by
      simp only [keysNodup, List.map_cons, List.nodup_cons] at hnd; exact hnd.1
    simp only [spendCoin, getCoin]
    by_cases h : k = op
    · subst h
      simp only [ite_true]
      -- no other entry has key k, so spendCoin rest k = rest
      have : spendCoin rest k = rest := by
        clear hnd hnd' c
        induction rest with
        | nil => rfl
        | cons e r ih =>
          simp only [List.map_cons, List.mem_cons, not_or] at hk
          rw [spendCoin, if_neg (fun h => hk.1 h.symm), ih hk.2]
      rw [this, totalValue_cons]; simp only []; omega
    · simp only [h, ite_false, totalValue_cons, totalValue_spendCoin rest op hnd']
      omega

private theorem getCoin_spendCoin_ne : ∀ (u : Ledger) (op op' : BitcoinSer.OutPoint), op ≠ op' →
    getCoin (spendCoin u op) op' = getCoin u op'
  | [], _, _, _ => rfl
  | (k, c) :: rest, op, op', h => by
    simp only [spendCoin, getCoin]
    by_cases hk : k = op
    · subst hk; simp only [ite_true, h, ite_false]; exact getCoin_spendCoin_ne rest k op' h
    · simp only [hk, ite_false, getCoin]
      by_cases hk' : k = op'
      · simp [hk']
      · simp only [hk', ite_false]; exact getCoin_spendCoin_ne rest op op' h

private theorem keysNodup_spendCoin : ∀ (u : Ledger) (op : BitcoinSer.OutPoint), keysNodup u → keysNodup (spendCoin u op)
  | [], _, h => h
  | (k, c) :: rest, op, h => by
    simp only [keysNodup, List.map_cons, List.nodup_cons] at h
    simp only [spendCoin]
    by_cases hk : k = op
    · simp only [hk, ite_true]; exact keysNodup_spendCoin rest op h.2
    · simp only [hk, ite_false, keysNodup, List.map_cons, List.nodup_cons]
      refine ⟨?_, keysNodup_spendCoin rest op h.2⟩
      intro hm; apply h.1
      -- keys of spendCoin rest op are a sublist of keys of rest
      have : ∀ (r : Ledger), k ∈ (spendCoin r op).map Prod.fst → k ∈ r.map Prod.fst := by
        intro r; induction r with
        | nil => intro h; exact h
        | cons e r ih =>
          simp only [spendCoin]
          by_cases he : e.1 = op
          · simp only [he, ite_true, List.map_cons, List.mem_cons]; intro h; exact Or.inr (ih h)
          · simp only [he, ite_false, List.map_cons, List.mem_cons]; intro h
            cases h with
            | inl h => exact Or.inl h
            | inr h => exact Or.inr (ih h)
      exact this rest hm

/-- Spending the inputs of a transaction with distinct prevouts that are all present removes
exactly `valueIn`. -/
private theorem totalValue_spendInputs : ∀ (ins : List BitcoinSer.TxIn) (u : Ledger), keysNodup u →
    (ins.map BitcoinSer.TxIn.prevout).Nodup → (∀ i ∈ ins, haveCoin u i.prevout = true) →
    totalValue (spendInputs u ins) = totalValue u - valueIn u ins
  | [], u, _, _, _ => by simp [spendInputs, valueIn]
  | i :: rest, u, hnd, hdup, hall => by
    simp only [spendInputs, valueIn]
    simp only [List.map_cons, List.nodup_cons] at hdup
    have hrest : ∀ j ∈ rest, haveCoin (spendCoin u i.prevout) j.prevout = true := by
      intro j hj
      have hne : i.prevout ≠ j.prevout := fun h => hdup.1 (h ▸ List.mem_map_of_mem hj)
      simp only [haveCoin, getCoin_spendCoin_ne u _ _ hne]
      exact hall j (List.mem_cons_of_mem _ hj)
    rw [totalValue_spendInputs rest _ (keysNodup_spendCoin u _ hnd) hdup.2 hrest]
    rw [totalValue_spendCoin u _ hnd]
    have hvi : valueIn (spendCoin u i.prevout) rest = valueIn u rest := by
      clear hrest hall
      induction rest with
      | nil => rfl
      | cons j r ih =>
        simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hdup
        simp only [valueIn, accessCoin]
        have hne : i.prevout ≠ j.prevout := fun h => hdup.1.1 h
        rw [getCoin_spendCoin_ne u _ _ hne]
        rw [ih ⟨fun h => hdup.1.2 h, hdup.2.2⟩]
    rw [hvi]
    have hi := hall i (List.mem_cons_self ..)
    simp only [haveCoin, Option.isSome] at hi
    simp only [accessCoin]
    cases hg : getCoin u i.prevout with
    | none => rw [hg] at hi; cases hi
    | some c => dsimp only [Option.getD]; omega

/-- Adding a coin raises the total by at most its value when every stored coin is non-negative. -/
private theorem totalValue_addCoin (u : Ledger) (op : BitcoinSer.OutPoint) (c : Coin) (hnd : keysNodup u)
    (hnn : ∀ e ∈ u, 0 ≤ e.2.out.nValue) (hc : 0 ≤ c.out.nValue) :
    totalValue (addCoin u op c) ≤ totalValue u + c.out.nValue := by
  simp only [addCoin]
  by_cases hu : isUnspendable c.out.scriptPubKey = true
  · simp only [hu, ite_true]; omega
  · simp only [hu, Bool.false_eq_true, ite_false, totalValue_cons, totalValue_spendCoin u op hnd]
    cases hg : getCoin u op with
    | none => simp only []; omega
    | some d =>
      simp only []
      have : 0 ≤ d.out.nValue := by
        have hm : (op, d) ∈ u := by
          clear hnn hnd hu
          induction u with
          | nil => simp [getCoin] at hg
          | cons e r ih =>
            simp only [getCoin] at hg
            by_cases he : e.1 = op
            · simp only [he, ite_true, Option.some.injEq] at hg; subst hg; simp [← he]
            · simp only [he, ite_false] at hg; exact List.mem_cons_of_mem _ (ih hg)
        exact hnn _ hm
      omega

private theorem spendCoin_sublist : ∀ (u : Ledger) (op : BitcoinSer.OutPoint), (spendCoin u op).Sublist u
  | [], _ => List.Sublist.slnil
  | (k, c) :: rest, op => by
    simp only [spendCoin]
    by_cases h : k = op
    · simp only [h, ite_true]; exact List.Sublist.cons _ (spendCoin_sublist rest op)
    · simp only [h, ite_false]; exact List.Sublist.cons₂ _ (spendCoin_sublist rest op)

private theorem keysNodup_addCoin (u : Ledger) (op : BitcoinSer.OutPoint) (c : Coin) (h : keysNodup u) :
    keysNodup (addCoin u op c) := by
  simp only [addCoin]
  split
  · exact h
  · simp only [keysNodup, List.map_cons, List.nodup_cons]
    refine ⟨?_, keysNodup_spendCoin u op h⟩
    -- op is not a key of spendCoin u op
    have : ∀ (r : Ledger), op ∉ (spendCoin r op).map Prod.fst := by
      intro r; induction r with
      | nil => simp [spendCoin]
      | cons e r ih =>
        simp only [spendCoin]
        by_cases he : e.1 = op
        · simp only [he, ite_true]; exact ih
        · simp only [he, ite_false, List.map_cons, List.mem_cons, not_or]
          exact ⟨fun h => he h.symm, ih⟩
    exact this u

/-- `addCoinsFrom` adds at most the values of the outputs. -/
private theorem totalValue_addCoinsFrom (txid : BitcoinSer.Bytes) (H : Nat) (cb : Bool) :
    ∀ (os : List BitcoinSer.TxOut) (u : Ledger) (i : Nat), keysNodup u → (∀ e ∈ u, 0 ≤ e.2.out.nValue) →
    (∀ o ∈ os, 0 ≤ o.nValue) →
    totalValue (addCoinsFrom txid H cb u i os) ≤ totalValue u + sumValues os
  | [], u, i, _, _, _ => by simp [addCoinsFrom, sumValues]
  | o :: rest, u, i, hnd, hnn, hos => by
    simp only [addCoinsFrom, sumValues]
    have hnd' : keysNodup (addCoin u ⟨txid, i⟩ ⟨o, H, cb⟩) := keysNodup_addCoin u _ _ hnd
    have hnn' : ∀ e ∈ addCoin u ⟨txid, i⟩ ⟨o, H, cb⟩, 0 ≤ e.2.out.nValue := by
      intro e he
      simp only [addCoin] at he
      split at he
      · exact hnn e he
      · simp only [List.mem_cons] at he
        cases he with
        | inl h => subst h; exact hos o (List.mem_cons_self ..)
        | inr h => exact hnn e (List.Sublist.subset (spendCoin_sublist u _) h)
    have ih := totalValue_addCoinsFrom txid H cb rest _ (i + 1) hnd' hnn' (fun o' h => hos o' (List.mem_cons_of_mem _ h))
    have ha : totalValue (addCoin u ⟨txid, i⟩ ⟨o, H, cb⟩) ≤ totalValue u + o.nValue :=
      totalValue_addCoin u ⟨txid, i⟩ ⟨o, H, cb⟩ hnd hnn (hos o (List.mem_cons_self ..))
    omega

private theorem mem_spendCoin : ∀ (u : Ledger) (op : BitcoinSer.OutPoint) (e : BitcoinSer.OutPoint × Coin),
    e ∈ spendCoin u op → e ∈ u :=
  fun u op e h => List.Sublist.subset (spendCoin_sublist u op) h

private theorem mem_spendInputs : ∀ (ins : List BitcoinSer.TxIn) (u : Ledger) (e : BitcoinSer.OutPoint × Coin),
    e ∈ spendInputs u ins → e ∈ u
  | [], u, e, h => h
  | i :: rest, u, e, h => mem_spendCoin u _ e (mem_spendInputs rest _ e h)

private theorem keysNodup_spendInputs : ∀ (ins : List BitcoinSer.TxIn) (u : Ledger), keysNodup u →
    keysNodup (spendInputs u ins)
  | [], u, h => h
  | i :: rest, u, h => keysNodup_spendInputs rest _ (keysNodup_spendCoin u _ h)

private theorem mem_addCoinsFrom (txid : BitcoinSer.Bytes) (H : Nat) (cb : Bool) :
    ∀ (os : List BitcoinSer.TxOut) (u : Ledger) (i : Nat) (e : BitcoinSer.OutPoint × Coin),
    e ∈ addCoinsFrom txid H cb u i os → e ∈ u ∨ e.2.out ∈ os
  | [], u, i, e, h => Or.inl h
  | o :: rest, u, i, e, h => by
    simp only [addCoinsFrom] at h
    cases mem_addCoinsFrom txid H cb rest _ (i + 1) e h with
    | inr h => exact Or.inr (List.mem_cons_of_mem _ h)
    | inl h =>
      simp only [addCoin] at h
      split at h
      · exact Or.inl h
      · simp only [List.mem_cons] at h
        cases h with
        | inl h => subst h; exact Or.inr (List.mem_cons_self ..)
        | inr h => exact Or.inl (mem_spendCoin u _ e h)

private theorem keysNodup_addCoinsFrom (txid : BitcoinSer.Bytes) (H : Nat) (cb : Bool) :
    ∀ (os : List BitcoinSer.TxOut) (u : Ledger) (i : Nat), keysNodup u → keysNodup (addCoinsFrom txid H cb u i os)
  | [], u, i, h => h
  | o :: rest, u, i, h => keysNodup_addCoinsFrom txid H cb rest _ (i + 1) (keysNodup_addCoin u _ _ h)

private theorem mem_updateCoins (u : Ledger) (tx : BitcoinSer.Tx) (H : Nat) (e : BitcoinSer.OutPoint × Coin)
    (h : e ∈ updateCoins u tx H) : e ∈ u ∨ e.2.out ∈ tx.vout := by
  simp only [updateCoins] at h
  cases mem_addCoinsFrom _ _ _ _ _ _ e h with
  | inr h => exact Or.inr h
  | inl h =>
    split at h
    · exact Or.inl h
    · exact Or.inl (mem_spendInputs _ _ _ h)

private theorem keysNodup_updateCoins (u : Ledger) (tx : BitcoinSer.Tx) (H : Nat) (h : keysNodup u) :
    keysNodup (updateCoins u tx H) := by
  simp only [updateCoins]
  apply keysNodup_addCoinsFrom
  split
  · exact h
  · exact keysNodup_spendInputs _ _ h

private theorem mem_applyTxs (H : Nat) : ∀ (txs : List BitcoinSer.Tx) (u : Ledger) (e : BitcoinSer.OutPoint × Coin),
    e ∈ applyTxs H u txs → e ∈ u ∨ ∃ tx ∈ txs, e.2.out ∈ tx.vout
  | [], u, e, h => Or.inl h
  | tx :: rest, u, e, h => by
    simp only [applyTxs] at h
    cases mem_applyTxs H rest _ e h with
    | inr h => exact Or.inr (let ⟨t, ht, hm⟩ := h; ⟨t, List.mem_cons_of_mem _ ht, hm⟩)
    | inl h =>
      cases mem_updateCoins u tx H e h with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr ⟨tx, List.mem_cons_self .., h⟩

/-- `UpdateCoins` changes the total by at most the value created minus (for a non-coinbase) the
value spent. -/
theorem solution (u : Ledger) (tx : BitcoinSer.Tx) (H : Nat) (hnd : BitcoinBlockV2.keysNodup u)
    (hnn : ∀ e ∈ u, 0 ≤ e.2.out.nValue) (hos : ∀ o ∈ tx.vout, 0 ≤ o.nValue)
    (hdup : (tx.vin.map BitcoinSer.TxIn.prevout).Nodup)
    (hin : BitcoinBlockV2.isCoinBase tx = false → ∀ i ∈ tx.vin, BitcoinBlockV2.haveCoin u i.prevout = true) :
    BitcoinSupply.totalValue (BitcoinBlockV2.updateCoins u tx H) ≤
      BitcoinSupply.totalValue u + BitcoinBlockV2.valueOut tx -
        (if BitcoinBlockV2.isCoinBase tx then 0 else BitcoinBlockV2.valueIn u tx.vin) := by
  simp only [updateCoins, valueOut]
  by_cases hcb : isCoinBase tx = true
  · simp only [hcb, ite_true]
    have := totalValue_addCoinsFrom (BitcoinSer.txid tx) H true tx.vout u 0 hnd hnn hos
    omega
  · simp only [hcb, Bool.false_eq_true, ite_false]
    have hcb' : isCoinBase tx = false := by simpa using hcb
    have hs := totalValue_spendInputs tx.vin u hnd hdup (hin hcb')
    have hnn' : ∀ e ∈ spendInputs u tx.vin, 0 ≤ e.2.out.nValue := fun e he => hnn e (mem_spendInputs _ _ _ he)
    have := totalValue_addCoinsFrom (BitcoinSer.txid tx) H false tx.vout _ 0 (keysNodup_spendInputs _ _ hnd) hnn' hos
    omega

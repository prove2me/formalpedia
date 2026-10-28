-- Prove2me | solution 1 for BitcoinBlockV2.reachable_wellFormed
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:22:47.119374+00:00
-- url     : https://prove2.me/submissions/01d08e5e-e7be-49fa-b6e5-5c7164a5518e

import Definitions.Def_BitcoinBlockV2

open BitcoinBlockV2 in
def S190BLK_Inv (u : Ledger) (H : Nat) : Prop :=
  keysNodup u ∧ ∀ e ∈ u, 1 ≤ e.2.height ∧ e.2.height ≤ H ∧ isUnspendable e.2.out.scriptPubKey = false

open BitcoinBlockV2 in
theorem S190BLK_spend_eq (u : Ledger) (op : BitcoinSer.OutPoint) :
    spendCoin u op = u.filter (fun e => !decide (e.1 = op)) := by
  induction u with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, c⟩ := e
    unfold spendCoin
    by_cases h : k = op
    · simp [h, ih]
    · simp [h, ih]

open BitcoinBlockV2 in
theorem S190BLK_inv_mono (u : Ledger) (H H' : Nat) (h : S190BLK_Inv u H) (hle : H ≤ H') : S190BLK_Inv u H' :=
  ⟨h.1, fun e he => let ⟨a, b, c⟩ := h.2 e he; ⟨a, by omega, c⟩⟩

open BitcoinBlockV2 in
theorem S190BLK_inv_spend (u : Ledger) (H : Nat) (op : BitcoinSer.OutPoint) (h : S190BLK_Inv u H) :
    S190BLK_Inv (spendCoin u op) H := by
  rw [S190BLK_spend_eq]
  refine ⟨?_, fun e he => h.2 e (List.mem_filter.mp he).1⟩
  unfold keysNodup
  exact List.Nodup.sublist (List.Sublist.map _ (List.filter_sublist)) h.1

open BitcoinBlockV2 in
theorem S190BLK_inv_add (u : Ledger) (H : Nat) (op : BitcoinSer.OutPoint) (c : Coin) (h : S190BLK_Inv u H)
    (h1 : 1 ≤ c.height) (h2 : c.height ≤ H) : S190BLK_Inv (addCoin u op c) H := by
  unfold addCoin
  by_cases hu : isUnspendable c.out.scriptPubKey = true
  · simp [hu, h]
  · simp only [hu, Bool.false_eq_true, if_false]
    have hs := S190BLK_inv_spend u H op h
    refine ⟨?_, ?_⟩
    · unfold keysNodup
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, hs.1⟩
      rw [S190BLK_spend_eq]
      simp
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with he | he
      · subst he; exact ⟨h1, h2, by simpa using hu⟩
      · exact hs.2 e he

open BitcoinBlockV2 in
theorem S190BLK_inv_addFrom (txid : BitcoinSer.Bytes) (H : Nat) (cb : Bool) (l : List BitcoinSer.TxOut)
    (u : Ledger) (i : Nat) (h : S190BLK_Inv u H) (h1 : 1 ≤ H) : S190BLK_Inv (addCoinsFrom txid H cb u i l) H := by
  induction l generalizing u i with
  | nil => exact h
  | cons o rest ih =>
    unfold addCoinsFrom
    exact ih _ _ (S190BLK_inv_add _ _ _ _ h h1 (Nat.le_refl _))

open BitcoinBlockV2 in
theorem S190BLK_inv_spendInputs (u : Ledger) (H : Nat) (l : List BitcoinSer.TxIn) (h : S190BLK_Inv u H) :
    S190BLK_Inv (spendInputs u l) H := by
  induction l generalizing u with
  | nil => exact h
  | cons i rest ih => exact ih _ (S190BLK_inv_spend _ _ _ h)

open BitcoinBlockV2 in
theorem S190BLK_inv_apply (H : Nat) (txs : List BitcoinSer.Tx) (u : Ledger) (h : S190BLK_Inv u H) (h1 : 1 ≤ H) :
    S190BLK_Inv (applyTxs H u txs) H := by
  induction txs generalizing u with
  | nil => exact h
  | cons tx rest ih =>
    apply ih
    unfold updateCoins
    apply S190BLK_inv_addFrom _ _ _ _ _ _ _ h1
    split
    · exact h
    · exact S190BLK_inv_spendInputs _ _ _ h


open BitcoinBlockV2 in
theorem S190BLK_loop_utxo (f : BitcoinActivation.ScriptFlags) (H : Nat) (mtp : Nat → Nat) (ltf : Nat)
    (txs : List BitcoinSer.Tx) (st st' : LoopState) (h : connectLoop f H mtp ltf st txs = some st') :
    st'.utxo = applyTxs H st.utxo txs := by
  induction txs generalizing st with
  | nil => simp [connectLoop] at h; subst h; rfl
  | cons tx rest ih =>
    unfold connectLoop at h
    simp only at h
    split at h
    · cases h
    · rename_i fees undo _
      split at h
      · cases h
      · split at h
        · cases h
        · exact ih _ h

open BitcoinBlockV2 in
theorem S190BLK_cb_apply (S : ChainState) (b : BitcoinSer.Block) (u : Ledger) (undo : BlockUndo)
    (h : connectBlock S b = some (u, undo)) : u = (applySpec S b).utxo := by
  unfold connectBlock at h
  unfold applySpec
  by_cases hg : BitcoinSer.headerHash b.header = BitcoinSer.genesisHash
  · simp only [hg, if_true] at h ⊢
    cases h; rfl
  · simp only [hg, if_false] at h ⊢
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i st hl
        split at h
        · cases h
        · cases h
          exact S190BLK_loop_utxo _ _ _ _ _ _ _ hl

open BitcoinBlockV2 in
theorem S190BLK_ah_pow (S : ChainState) (h : BitcoinSer.Header) (now : Int) (S0 : ChainState) (u0 : BlockUndo)
    (hA : acceptHeader S h now = .accept S0 u0) : checkHeaderPow h = true := by
  unfold acceptHeader at hA
  cases hp : checkHeaderPow h
  · simp [hp] at hA
  · rfl

open BitcoinBlockV2 in
theorem S190BLK_val_acc (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState) (undo : BlockUndo)
    (h : validate S b now = .accept S' undo) :
    checkHeaderPow b.header = true ∧ checkBlock b = true ∧ contextualCheckBlock S b = true ∧
    connectBlock S b = some (S'.utxo, undo) ∧ S' = ⟨S.headers ++ [b.header], S'.utxo⟩ := by
  unfold validate at h
  split at h
  · rename_i S0 u0 hA
    have hp := S190BLK_ah_pow _ _ _ _ _ hA
    by_cases c1 : checkBlock b = true
    · by_cases c2 : contextualCheckBlock S b = true
      · simp only [c1, c2, Bool.not_true, Bool.false_eq_true, if_false] at h
        split at h
        · cases h
        · rename_i u un hc
          cases h
          exact ⟨hp, c1, c2, hc, rfl⟩
      · simp [c1, c2] at h
    · simp [c1] at h
  · rename_i o hno
    exact absurd h (hno S' undo)

open BitcoinBlockV2 in
theorem S190BLK_apply_spec (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState) (undo : BlockUndo)
    (h : BitcoinBlockV2.validate S b now = .accept S' undo) : S' = BitcoinBlockV2.applySpec S b := by
  obtain ⟨-, -, -, hc, hS⟩ := S190BLK_val_acc S b now S' undo h
  have hu := S190BLK_cb_apply S b _ _ hc
  have hh : (applySpec S b).headers = S.headers ++ [b.header] := by
    unfold applySpec; split <;> rfl
  rw [hS]
  cases hA : applySpec S b with
  | mk hd ut =>
    rw [hA] at hu hh
    simp only at hu hh
    rw [hu, hh]

open BitcoinBlockV2 in
theorem S190BLK_wf_step (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState) (undo : BlockUndo)
    (hwf : WellFormed S) (h : validate S b now = .accept S' undo) : WellFormed S' := by
  have hS := S190BLK_apply_spec S b now S' undo h
  subst hS
  obtain ⟨hhd, hnd, hall⟩ := hwf
  have hinv : S190BLK_Inv S.utxo S.headers.length := by
    refine ⟨hnd, fun e he => ?_⟩
    obtain ⟨a, b, c⟩ := hall e he
    unfold ChainState.tipHeight at b
    exact ⟨a, by omega, c⟩
  have hlen : 1 ≤ S.headers.length := by
    cases hh : S.headers with
    | nil => rw [hh] at hhd; cases hhd
    | cons _ _ => simp
  have key : ∀ (u : Ledger), S190BLK_Inv u S.headers.length →
      WellFormed ⟨S.headers ++ [b.header], u⟩ := by
    intro u hu
    refine ⟨?_, hu.1, fun e he => ?_⟩
    · cases hh : S.headers with
      | nil => rw [hh] at hhd; cases hhd
      | cons x xs => rw [hh] at hhd; simpa using hhd
    · obtain ⟨a, b', c⟩ := hu.2 e he
      refine ⟨a, ?_, c⟩
      unfold ChainState.tipHeight
      simp only [List.length_append, List.length_singleton]
      omega
  unfold applySpec
  split
  · exact key _ hinv
  · exact key _ (S190BLK_inv_apply _ _ _ hinv hlen)

open BitcoinBlockV2 in
theorem solution (S : ChainState) (h : BitcoinBlockV2.Reachable S) :
    BitcoinBlockV2.WellFormed S := by
  induction h with
  | genesis =>
    refine ⟨rfl, ?_, ?_⟩
    · unfold keysNodup initialState; simp
    · intro e he; simp [initialState] at he
  | step _ hv ih => exact S190BLK_wf_step _ _ _ _ _ ih hv

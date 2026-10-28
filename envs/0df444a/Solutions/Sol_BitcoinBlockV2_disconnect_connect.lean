-- Prove2me | solution 1 for BitcoinBlockV2.disconnect_connect
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:22:52.207559+00:00
-- url     : https://prove2.me/submissions/727d8ccb-a90f-4717-882c-f1d2d5b16564

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

open BitcoinBlockV2 in
theorem S190BLK_gs (u : Ledger) (op x : BitcoinSer.OutPoint) :
    getCoin (spendCoin u op) x = if op = x then none else getCoin u x := by
  induction u with
  | nil => simp [spendCoin, getCoin]
  | cons e rest ih =>
    obtain ⟨k, c⟩ := e
    unfold spendCoin
    by_cases h : k = op
    · subst h; simp only [if_true]; rw [ih]; by_cases hx : k = x <;> simp [hx, getCoin]
    · simp only [h, if_false, getCoin]; rw [ih]
      by_cases hx : k = x
      · subst hx; simp [Ne.symm h]
      · simp [hx]

open BitcoinBlockV2 in
theorem S190BLK_ga (u : Ledger) (op x : BitcoinSer.OutPoint) (c : Coin) :
    getCoin (addCoin u op c) x =
      if isUnspendable c.out.scriptPubKey = true then getCoin u x else if op = x then some c else getCoin u x := by
  unfold addCoin
  by_cases hu : isUnspendable c.out.scriptPubKey = true
  · simp [hu]
  · simp only [hu, Bool.false_eq_true, if_false, getCoin]
    rw [S190BLK_gs]
    by_cases hx : op = x <;> simp [hx]

open BitcoinBlockV2 in
theorem S190BLK_gsi (u : Ledger) (l : List BitcoinSer.TxIn) (x : BitcoinSer.OutPoint) :
    getCoin (spendInputs u l) x = if x ∈ l.map BitcoinSer.TxIn.prevout then none else getCoin u x := by
  induction l generalizing u with
  | nil => simp [spendInputs]
  | cons i rest ih =>
    unfold spendInputs
    rw [ih, S190BLK_gs]
    by_cases h1 : i.prevout = x
    · subst h1; simp
    · by_cases h2 : x ∈ rest.map BitcoinSer.TxIn.prevout
      · simp [h2]
      · simp only [h2, if_false, h1, List.map_cons, List.mem_cons]
        simp only [List.mem_map] at h2
        simp [h2]
        intro h; exact absurd h.symm h1

open BitcoinBlockV2 in
theorem S190BLK_gaf (t : BitcoinSer.Bytes) (H : Nat) (cb : Bool) (l : List BitcoinSer.TxOut)
    (u : Ledger) (i : Nat) (x : BitcoinSer.OutPoint) :
    getCoin (addCoinsFrom t H cb u i l) x =
      if x.hash = t ∧ i ≤ x.n ∧ x.n < i + l.length ∧
          isUnspendable (l.getD (x.n - i) ⟨0, []⟩).scriptPubKey = false then
        some ⟨l.getD (x.n - i) ⟨0, []⟩, H, cb⟩
      else getCoin u x := by
  induction l generalizing u i with
  | nil => simp [addCoinsFrom]; omega
  | cons o rest ih =>
    unfold addCoinsFrom
    rw [ih, S190BLK_ga]
    by_cases hx : x = ⟨t, i⟩
    · subst hx
      simp only [Nat.le_refl, Nat.sub_self, true_and, List.length_cons]
      have : ¬ (i + 1 ≤ i) := by omega
      simp only [this, false_and, and_false, if_false, List.getD_cons_zero]
      by_cases hu : isUnspendable o.scriptPubKey = true
      · simp [hu]
      · simp [hu]
    · have hx' : ¬ (BitcoinSer.OutPoint.mk t i = x) := fun h => hx h.symm
      simp only [hx', if_false, ite_self]
      by_cases hh : x.hash = t
      · have hn : x.n ≠ i := by
          intro hn; apply hx; cases x; simp_all
        by_cases hl : i + 1 ≤ x.n
        · have e2 : x.n - i = (x.n - (i + 1)) + 1 := by omega
          simp only [hh, true_and, List.length_cons, e2, List.getD_cons_succ]
          have : i ≤ x.n := by omega
          simp only [hl, this, true_and]
          have : (x.n < i + 1 + rest.length) ↔ (x.n < i + (rest.length + 1)) := by omega
          simp only [this]
        · have : ¬ (i ≤ x.n ∧ x.n < i + (rest.length + 1) ∧ isUnspendable ((o :: rest).getD (x.n - i) ⟨0, []⟩).scriptPubKey = false) := by
            rintro ⟨h1, -, -⟩; omega
          simp only [hh, true_and, hl, false_and, if_false, List.length_cons]
          rw [if_neg this]
      · simp [hh]

open BitcoinBlockV2 in
theorem S190BLK_so (t : BitcoinSer.Bytes) (H : Nat) (cb exc : Bool) (l : List BitcoinSer.TxOut) (v : Ledger) (i : Nat)
    (hv : ∀ j, j < l.length → getCoin v ⟨t, i + j⟩ =
      if isUnspendable (l.getD j ⟨0, []⟩).scriptPubKey = true then none else some ⟨l.getD j ⟨0, []⟩, H, cb⟩) :
    (spendOutputs v t H cb exc l i).2 = true ∧
    ∀ x, getCoin (spendOutputs v t H cb exc l i).1 x =
      if x.hash = t ∧ i ≤ x.n ∧ x.n < i + l.length then none else getCoin v x := by
  induction l generalizing v i with
  | nil => simp [spendOutputs]; intro x h1 h2; omega
  | cons o rest ih =>
    by_cases hu : isUnspendable o.scriptPubKey = true
    · have hv' : ∀ j, j < rest.length → getCoin v ⟨t, (i + 1) + j⟩ =
          if isUnspendable (rest.getD j ⟨0, []⟩).scriptPubKey = true then none else some ⟨rest.getD j ⟨0, []⟩, H, cb⟩ := by
        intro j hj
        have := hv (j + 1) (by simp; omega)
        rw [show i + (j + 1) = i + 1 + j by omega] at this
        simpa using this
      obtain ⟨ih1, ih2⟩ := ih v (i + 1) hv'
      have h0 := hv 0 (by simp)
      simp only [Nat.add_zero, List.getD_cons_zero, hu, if_true] at h0
      simp only [spendOutputs, hu, if_true]
      refine ⟨by simpa using ih1, fun x => ?_⟩
      rw [ih2]
      by_cases hx : x = ⟨t, i⟩
      · subst hx; simp [h0]
      · by_cases hh : x.hash = t
        · have hn : x.n ≠ i := by intro hn; apply hx; cases x; simp_all
          simp only [hh, true_and, List.length_cons]
          by_cases hr : i + 1 ≤ x.n ∧ x.n < i + 1 + rest.length
          · rw [if_pos hr, if_pos (by omega)]
          · rw [if_neg hr, if_neg (by omega)]
        · simp [hh]
    · have hu' : isUnspendable o.scriptPubKey = false := by simpa using hu
      have h0 := hv 0 (by simp)
      simp only [Nat.add_zero, List.getD_cons_zero, hu', Bool.false_eq_true, if_false] at h0
      have hv' : ∀ j, j < rest.length → getCoin (spendCoin v ⟨t, i⟩) ⟨t, (i + 1) + j⟩ =
          if isUnspendable (rest.getD j ⟨0, []⟩).scriptPubKey = true then none else some ⟨rest.getD j ⟨0, []⟩, H, cb⟩ := by
        intro j hj
        rw [S190BLK_gs]
        have : ¬ (BitcoinSer.OutPoint.mk t i = ⟨t, i + 1 + j⟩) := by simp; omega
        rw [if_neg this]
        have := hv (j + 1) (by simp; omega)
        rw [show i + (j + 1) = i + 1 + j by omega] at this
        simpa using this
      obtain ⟨ih1, ih2⟩ := ih _ (i + 1) hv'
      simp only [spendOutputs, hu, Bool.false_eq_true, if_false, h0, decide_true, Bool.true_and, Bool.true_or]
      refine ⟨by simpa using ih1, fun x => ?_⟩
      rw [ih2, S190BLK_gs]
      by_cases hx : x = ⟨t, i⟩
      · subst hx; simp
      · have hx' : ¬ (BitcoinSer.OutPoint.mk t i = x) := fun h => hx h.symm
        rw [if_neg hx']
        by_cases hh : x.hash = t
        · have hn : x.n ≠ i := by intro hn; apply hx; cases x; simp_all
          simp only [hh, true_and, List.length_cons]
          by_cases hr : i + 1 ≤ x.n ∧ x.n < i + 1 + rest.length
          · rw [if_pos hr, if_pos (by omega)]
          · rw [if_neg hr, if_neg (by omega)]
        · simp [hh]

open BitcoinBlockV2 in
theorem S190BLK_ri (l : List (BitcoinSer.TxIn × Coin)) (w : Ledger)
    (hnd : (l.map (fun p => p.1.prevout)).Nodup)
    (hc : ∀ p ∈ l, p.2.height ≠ 0 ∧ isUnspendable p.2.out.scriptPubKey = false ∧ getCoin w p.1.prevout = none) :
    ∃ w', restoreInputs w l = some (w', true) ∧ (∀ p ∈ l, getCoin w' p.1.prevout = some p.2) ∧
      ∀ x, (∀ p ∈ l, p.1.prevout ≠ x) → getCoin w' x = getCoin w x := by
  induction l with
  | nil => exact ⟨w, rfl, by simp, fun _ _ => rfl⟩
  | cons p rest ih =>
    obtain ⟨i, c⟩ := p
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hn1, hn2⟩ := hnd
    obtain ⟨w1, hw1, hw2, hw3⟩ := ih hn2 (fun q hq => hc q (by simp [hq]))
    obtain ⟨hh, hsp, hnone⟩ := hc (i, c) (by simp)
    simp only at hh hsp hnone
    have hw1i : getCoin w1 i.prevout = none := by
      rw [hw3 i.prevout (fun q hq he => hn1 ⟨q, hq, he⟩)]; exact hnone
    refine ⟨addCoin w1 i.prevout c, ?_, ?_, ?_⟩
    · simp only [restoreInputs, hw1, applyTxInUndo, haveCoin, hw1i, hh, if_false]
      rfl
    · intro q hq
      simp only [List.mem_cons] at hq
      rw [S190BLK_ga]
      simp only [hsp, Bool.false_eq_true, if_false]
      rcases hq with hq | hq
      · subst hq; simp
      · have hne : i.prevout ≠ q.1.prevout := fun he => hn1 ⟨q, hq, he.symm⟩
        rw [if_neg hne]; exact hw2 q hq
    · intro x hx
      rw [S190BLK_ga]
      simp only [hsp, Bool.false_eq_true, if_false]
      have h1 : i.prevout ≠ x := hx (i, c) (by simp)
      rw [if_neg h1]
      exact hw3 x (fun q hq => hx q (by simp [hq]))

theorem S190BLK_zip_map {α β : Type} (l : List α) (g : α → β) : l.zip (l.map g) = l.map (fun a => (a, g a)) := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp [ih]

open BitcoinBlockV2 in
theorem S190BLK_dtx (u : Ledger) (tx : BitcoinSer.Tx) (H : Nat) (exc : Bool) (v : Ledger)
    (hfresh : ∀ o, getCoin u ⟨BitcoinSer.txid tx, o⟩ = none)
    (hcoins : ∀ x c, getCoin u x = some c → c.height ≠ 0 ∧ isUnspendable c.out.scriptPubKey = false)
    (hin : isCoinBase tx = false → (∀ i ∈ tx.vin, getCoin u i.prevout ≠ none) ∧ (tx.vin.map BitcoinSer.TxIn.prevout).Nodup)
    (hv : Equiv v (updateCoins u tx H)) :
    ∃ w, disconnectTx v H exc tx (if isCoinBase tx = true then none else some (txUndo u tx)) = some (w, true) ∧
      Equiv w u := by
  generalize ht : BitcoinSer.txid tx = t at hfresh
  have hpo : isCoinBase tx = false → ∀ i ∈ tx.vin, i.prevout.hash ≠ t := by
    intro hcb i hi he
    apply (hin hcb).1 i hi
    have : i.prevout = ⟨t, i.prevout.n⟩ := by cases hp : i.prevout; simp_all
    rw [this, hfresh]
  -- the ledger after connecting
  have hB : ∀ x, x.hash = t → getCoin (if isCoinBase tx = true then u else spendInputs u tx.vin) x = none := by
    intro x hx
    have hu : getCoin u x = none := by
      have : x = ⟨t, x.n⟩ := by cases x; simp_all
      rw [this, hfresh]
    split
    · exact hu
    · rename_i hcb
      rw [S190BLK_gsi]
      split
      · rfl
      · exact hu
  have hU1 : ∀ x, x.hash = t → getCoin (updateCoins u tx H) x =
      if x.n < tx.vout.length ∧ isUnspendable (tx.vout.getD x.n ⟨0, []⟩).scriptPubKey = false then
        some ⟨tx.vout.getD x.n ⟨0, []⟩, H, isCoinBase tx⟩ else none := by
    intro x hx
    unfold updateCoins
    rw [ht, S190BLK_gaf, hB x hx]
    simp [hx]
  have hU2 : ∀ x, x.hash ≠ t → getCoin (updateCoins u tx H) x =
      getCoin (if isCoinBase tx = true then u else spendInputs u tx.vin) x := by
    intro x hx
    unfold updateCoins
    rw [ht, S190BLK_gaf]
    simp [hx]
  have hso := S190BLK_so t H (isCoinBase tx) (isCoinBase tx && exc) tx.vout v 0 (by
    intro j hj
    rw [hv, hU1 _ rfl]
    simp only [Nat.zero_add]
    cases hu : isUnspendable (tx.vout.getD j ⟨0, []⟩).scriptPubKey <;> simp [hj])
  obtain ⟨hso1, hso2⟩ := hso
  generalize hsp : spendOutputs v t H (isCoinBase tx) (isCoinBase tx && exc) tx.vout 0 = r at hso1 hso2
  obtain ⟨v1, cl⟩ := r
  simp only at hso1 hso2
  subst hso1
  have hv1t : ∀ x, x.hash = t → getCoin v1 x = none := by
    intro x hx
    rw [hso2]
    by_cases hn : x.n < tx.vout.length
    · simp [hx, hn]
    · simp only [hx, true_and, Nat.zero_le, Nat.zero_add, hn, and_false, if_false]
      rw [hv, hU1 x hx]; simp [hn]
  have hv1o : ∀ x, x.hash ≠ t → getCoin v1 x = getCoin (if isCoinBase tx = true then u else spendInputs u tx.vin) x := by
    intro x hx
    rw [hso2]; simp only [hx, false_and, if_false]
    rw [hv, hU2 x hx]
  have hut : ∀ x, x.hash = t → getCoin u x = none := by
    intro x hx
    have : x = ⟨t, x.n⟩ := by cases x; simp_all
    rw [this, hfresh]
  unfold disconnectTx
  simp only [ht, hsp]
  cases hcb : isCoinBase tx
  · -- non-coinbase
    obtain ⟨hin1, hnd⟩ := hin hcb
    have hpo' := hpo hcb
    simp only [Bool.false_eq_true, if_false, txUndo, List.length_map, ne_eq, not_true_eq_false]
    rw [S190BLK_zip_map]
    obtain ⟨w, hw1, hw2, hw3⟩ := S190BLK_ri (tx.vin.map fun i => (i, accessCoin u i.prevout)) v1
      (by rw [List.map_map]; exact hnd)
      (by
        intro p hp
        simp only [List.mem_map] at hp
        obtain ⟨i, hi, rfl⟩ := hp
        obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (hin1 i hi)
        simp only [accessCoin, hc, Option.getD_some]
        obtain ⟨a, b⟩ := hcoins _ _ hc
        refine ⟨a, b, ?_⟩
        rw [hv1o _ (hpo' i hi)]
        simp only [hcb, Bool.false_eq_true, if_false]
        rw [S190BLK_gsi]
        simp [List.mem_map]
        intro h; exact absurd rfl (h i hi))
    simp only [hw1]
    refine ⟨w, rfl, fun x => ?_⟩
    by_cases hx : ∃ i ∈ tx.vin, i.prevout = x
    · obtain ⟨i, hi, rfl⟩ := hx
      have := hw2 (i, accessCoin u i.prevout) (List.mem_map.mpr ⟨i, hi, rfl⟩)
      rw [this]
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (hin1 i hi)
      simp [accessCoin, hc]
    · have hx' : ∀ p ∈ tx.vin.map (fun i => (i, accessCoin u i.prevout)), p.1.prevout ≠ x := by
        intro p hp
        simp only [List.mem_map] at hp
        obtain ⟨i, hi, rfl⟩ := hp
        exact fun he => hx ⟨i, hi, he⟩
      rw [hw3 x hx']
      by_cases hh : x.hash = t
      · rw [hv1t x hh, hut x hh]
      · rw [hv1o x hh]
        simp only [hcb, Bool.false_eq_true, if_false]
        rw [S190BLK_gsi]
        have : x ∉ tx.vin.map BitcoinSer.TxIn.prevout := by
          simp only [List.mem_map]; exact hx
        simp [this]
  · -- coinbase
    simp only [if_true]
    refine ⟨v1, rfl, fun x => ?_⟩
    by_cases hh : x.hash = t
    · rw [hv1t x hh, hut x hh]
    · rw [hv1o x hh]; simp [hcb]

open BitcoinBlockV2 in
theorem S190BLK_dtxs_app (H : Nat) (exc : Bool) (A B : List (BitcoinSer.Tx × Option (List Coin))) (v w1 w2 : Ledger)
    (h1 : disconnectTxs H exc v A = some (w1, true)) (h2 : disconnectTxs H exc w1 B = some (w2, true)) :
    disconnectTxs H exc v (A ++ B) = some (w2, true) := by
  induction A generalizing v with
  | nil => simp [disconnectTxs] at h1; obtain ⟨rfl, -⟩ := h1; simpa using h2
  | cons p rest ih =>
    obtain ⟨tx, un⟩ := p
    simp only [disconnectTxs] at h1 ⊢
    cases hd : disconnectTx v H exc tx un with
    | none => simp [hd] at h1
    | some r =>
      obtain ⟨v1, c1⟩ := r
      simp only [hd] at h1 ⊢
      cases hr : disconnectTxs H exc v1 rest with
      | none => simp [hr] at h1
      | some r2 =>
        obtain ⟨v2, c2⟩ := r2
        simp only [hr, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true] at h1
        obtain ⟨rfl, rfl, rfl⟩ := h1
        rw [List.cons_append]
        simp only [disconnectTxs, hd, List.cons_append]
        rw [ih v1 hr]
        rfl

open BitcoinBlockV2 in
theorem S190BLK_cti_have (u : Ledger) (tx : BitcoinSer.Tx) (H : Nat) (fee : Int)
    (h : checkTxInputs u tx H = some fee) : ∀ i ∈ tx.vin, getCoin u i.prevout ≠ none := by
  unfold checkTxInputs at h
  by_cases ha : (tx.vin.all fun i => haveCoin u i.prevout) = true
  · intro i hi
    have := List.all_eq_true.mp ha i hi
    simp only [haveCoin, Option.isSome_iff_ne_none] at this
    exact this
  · simp [ha] at h

open BitcoinBlockV2 in
theorem S190BLK_loop_step (f : BitcoinActivation.ScriptFlags) (H : Nat) (mtp : Nat → Nat) (ltf : Nat)
    (tx : BitcoinSer.Tx) (rest : List BitcoinSer.Tx) (st st' : LoopState)
    (h : connectLoop f H mtp ltf st (tx :: rest) = some st') :
    ∃ st1 : LoopState, st1.utxo = updateCoins st.utxo tx H ∧
      st1.undo = st.undo ++ (if isCoinBase tx = true then [] else [txUndo st.utxo tx]) ∧
      (isCoinBase tx = false → ∃ fee, checkTxInputs st.utxo tx H = some fee) ∧
      connectLoop f H mtp ltf st1 rest = some st' := by
  unfold connectLoop at h
  simp only at h
  by_cases hcb : isCoinBase tx = true
  · simp only [hcb, if_true] at h
    split at h
    · cases h
    · split at h
      · cases h
      · exact ⟨_, rfl, by simp [hcb], by simp [hcb], h⟩
  · have hcb' : isCoinBase tx = false := by simpa using hcb
    simp only [hcb', Bool.false_eq_true, if_false] at h
    cases hc : checkTxInputs st.utxo tx H with
    | none => simp [hc] at h
    | some fee =>
      simp only [hc] at h
      by_cases hm : moneyRange (st.fees + fee) = true
      · by_cases hq : sequenceLocksOk st.utxo H mtp ltf tx = true
        · simp only [hm, hq, Bool.not_true, Bool.false_eq_true, if_false] at h
          split at h
          · cases h
          · split at h
            · cases h
            · exact ⟨_, rfl, by simp [hcb'], fun _ => ⟨fee, rfl⟩, h⟩
        · simp [hm, hq] at h
      · simp [hm] at h

open BitcoinBlockV2 in
theorem S190BLK_dloop (f : BitcoinActivation.ScriptFlags) (H : Nat) (mtp : Nat → Nat) (ltf : Nat) (exc : Bool)
    (hH : 1 ≤ H) (txs : List BitcoinSer.Tx) (st st' : LoopState)
    (h : connectLoop f H mtp ltf st txs = some st')
    (hfresh : ∀ tx ∈ txs, ∀ o, getCoin st.utxo ⟨BitcoinSer.txid tx, o⟩ = none)
    (hnd : (txs.map BitcoinSer.txid).Nodup)
    (hcoins : ∀ x c, getCoin st.utxo x = some c → c.height ≠ 0 ∧ isUnspendable c.out.scriptPubKey = false)
    (hpv : ∀ tx ∈ txs, (tx.vin.map BitcoinSer.TxIn.prevout).Nodup) :
    ∃ pairs : List (BitcoinSer.Tx × Option (List Coin)), pairs.map Prod.fst = txs ∧
      st'.undo = st.undo ++ pairs.filterMap Prod.snd ∧
      (∀ p ∈ pairs, (isCoinBase p.1 = true ↔ p.2 = none)) ∧
      ∀ v, Equiv v st'.utxo → ∃ w, disconnectTxs H exc v pairs.reverse = some (w, true) ∧ Equiv w st.utxo := by
  induction txs generalizing st with
  | nil =>
    simp [connectLoop] at h; subst h
    refine ⟨[], rfl, by simp, by simp, fun v hv => ⟨v, rfl, hv⟩⟩
  | cons tx rest ih =>
    obtain ⟨st1, h1u, h1d, h1c, h1l⟩ := S190BLK_loop_step f H mtp ltf tx rest st st' h
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hnd1, hnd2⟩ := hnd
    have hB : ∀ x, getCoin (if isCoinBase tx = true then st.utxo else spendInputs st.utxo tx.vin) x = none ∨
        getCoin (if isCoinBase tx = true then st.utxo else spendInputs st.utxo tx.vin) x = getCoin st.utxo x := by
      intro x
      split
      · right; rfl
      · rw [S190BLK_gsi]; split
        · left; rfl
        · right; rfl
    have hfresh1 : ∀ tx' ∈ rest, ∀ o, getCoin st1.utxo ⟨BitcoinSer.txid tx', o⟩ = none := by
      intro tx' ht' o
      rw [h1u]; unfold updateCoins; rw [S190BLK_gaf]
      have hne : BitcoinSer.txid tx' ≠ BitcoinSer.txid tx := fun he => hnd1 ⟨tx', ht', he⟩
      simp only [hne, false_and, if_false]
      rcases hB ⟨BitcoinSer.txid tx', o⟩ with hb | hb
      · exact hb
      · rw [hb]; exact hfresh tx' (by simp [ht']) o
    have hcoins1 : ∀ x c, getCoin st1.utxo x = some c → c.height ≠ 0 ∧ isUnspendable c.out.scriptPubKey = false := by
      intro x c hc
      rw [h1u] at hc; unfold updateCoins at hc; rw [S190BLK_gaf] at hc
      split at hc
      · rename_i hcond
        cases hc
        exact ⟨by simp; omega, hcond.2.2.2⟩
      · rcases hB x with hb | hb
        · rw [hb] at hc; cases hc
        · rw [hb] at hc; exact hcoins x c hc
    obtain ⟨pr, hpr1, hpr2, hpr3, hpr4⟩ := ih st1 h1l hfresh1 hnd2 hcoins1 (fun t ht => hpv t (by simp [ht]))
    let p : BitcoinSer.Tx × Option (List Coin) := (tx, if isCoinBase tx = true then none else some (txUndo st.utxo tx))
    refine ⟨p :: pr, by simp [p, hpr1], ?_, ?_, ?_⟩
    · rw [hpr2, h1d]
      cases hcb : isCoinBase tx <;> simp [p, hcb]
    · intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hcb : isCoinBase tx <;> simp [p, hcb]
      · exact hpr3 q hq
    · intro v hv
      obtain ⟨w1, hw1, hw1e⟩ := hpr4 v hv
      have hin : isCoinBase tx = false → (∀ i ∈ tx.vin, getCoin st.utxo i.prevout ≠ none) ∧
          (tx.vin.map BitcoinSer.TxIn.prevout).Nodup := by
        intro hcb
        obtain ⟨fee, hf⟩ := h1c hcb
        exact ⟨S190BLK_cti_have _ _ _ _ hf, hpv tx (by simp)⟩
      obtain ⟨w2, hw2, hw2e⟩ := S190BLK_dtx st.utxo tx H exc w1 (hfresh tx (by simp)) hcoins hin
        (fun x => by rw [hw1e x, h1u])
      refine ⟨w2, ?_, hw2e⟩
      rw [List.reverse_cons]
      apply S190BLK_dtxs_app H exc _ _ v w1 w2 hw1
      simp only [disconnectTxs, p, hw2]
      rfl

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
theorem S190BLK_getCoin_mem (u : Ledger) (x : BitcoinSer.OutPoint) (c : Coin) (h : getCoin u x = some c) :
    (x, c) ∈ u := by
  induction u with
  | nil => cases h
  | cons e rest ih =>
    obtain ⟨k, c'⟩ := e
    simp only [getCoin] at h
    by_cases hk : k = x
    · simp only [hk, if_true, Option.some.injEq] at h; subst hk; subst h; simp
    · simp only [hk, if_false] at h; exact List.mem_cons_of_mem _ (ih h)

open BitcoinBlockV2 in
theorem S190BLK_zip_pairs (pr : List (BitcoinSer.Tx × Option (List Coin))) (h : ∀ q ∈ pr, q.2 ≠ none) :
    (pr.map Prod.fst).zip ((pr.filterMap Prod.snd).map some) = pr := by
  induction pr with
  | nil => rfl
  | cons q rest ih =>
    obtain ⟨tx, un⟩ := q
    cases un with
    | none => exact absurd rfl (h (tx, none) (by simp))
    | some U =>
      have := ih (fun q hq => h q (by simp [hq]))
      simp [List.filterMap_cons, this]

open BitcoinBlockV2 in
theorem S190BLK_len_pairs (pr : List (BitcoinSer.Tx × Option (List Coin))) (h : ∀ q ∈ pr, q.2 ≠ none) :
    (pr.filterMap Prod.snd).length = pr.length := by
  induction pr with
  | nil => rfl
  | cons q rest ih =>
    obtain ⟨tx, un⟩ := q
    cases un with
    | none => exact absurd rfl (h (tx, none) (by simp))
    | some U =>
      have := ih (fun q hq => h q (by simp [hq]))
      simp [List.filterMap_cons, this]

open BitcoinBlockV2 in
theorem solution (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState)
    (undo : BlockUndo) (hwf : BitcoinBlockV2.WellFormed S) (hnd : (b.vtx.map BitcoinSer.txid).Nodup)
    (hfresh : ∀ tx ∈ b.vtx, ∀ o, BitcoinBlockV2.getCoin S.utxo ⟨BitcoinSer.txid tx, o⟩ = none)
    (hg : BitcoinSer.headerHash b.header ≠ BitcoinSer.genesisHash)
    (h : BitcoinBlockV2.validate S b now = .accept S' undo) :
    ∃ u, BitcoinBlockV2.disconnectBlock S'.utxo S.nextHeight (BitcoinSer.headerHash b.header) b undo = some (u, true) ∧
      BitcoinBlockV2.Equiv u S.utxo := by
  obtain ⟨-, hchk, -, hcon, -⟩ := S190BLK_val_acc S b now S' undo h
  obtain ⟨hhd, -, hall⟩ := hwf
  have hH : 1 ≤ S.nextHeight := by
    unfold ChainState.nextHeight
    cases hh : S.headers with
    | nil => rw [hh] at hhd; cases hhd
    | cons _ _ => simp
  have hcoins : ∀ x c, getCoin S.utxo x = some c → c.height ≠ 0 ∧ isUnspendable c.out.scriptPubKey = false := by
    intro x c hc
    obtain ⟨a, -, c2⟩ := hall _ (S190BLK_getCoin_mem _ _ _ hc)
    exact ⟨by simp at a; omega, c2⟩
  unfold checkBlock at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hne⟩, -⟩, -⟩, hcb0⟩, hrest⟩, htx⟩, -⟩ := hchk
  have hpv : ∀ tx ∈ b.vtx, (tx.vin.map BitcoinSer.TxIn.prevout).Nodup := by
    intro tx ht
    have := htx tx ht
    unfold checkTransaction at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.2
  unfold connectBlock at hcon
  simp only [hg, if_false] at hcon
  split at hcon
  · cases hcon
  · split at hcon
    · cases hcon
    · rename_i st hl
      split at hcon
      · cases hcon
      · simp only [Option.some.injEq, Prod.mk.injEq] at hcon
        obtain ⟨hu, hund⟩ := hcon
        obtain ⟨pairs, hp1, hp2, hp3, hp4⟩ := S190BLK_dloop _ _ _ _
          (isBIP30Unspendable S.nextHeight (BitcoinSer.headerHash b.header)) hH b.vtx _ st hl
          hfresh hnd hcoins hpv
        simp only [List.nil_append] at hp2
        obtain ⟨w, hw1, hw2⟩ := hp4 S'.utxo (by rw [hu]; intro x; rfl)
        refine ⟨w, ?_, hw2⟩
        cases hv : b.vtx with
        | nil => exact absurd hv hne
        | cons cb rest =>
          rw [hv] at hp1 hcb0 hrest
          cases pairs with
          | nil => cases hp1
          | cons p0 pr =>
            simp only [List.map_cons, List.cons.injEq] at hp1
            obtain ⟨hp0, hpr⟩ := hp1
            simp only [List.headD_cons] at hcb0
            have hp0n : p0.2 = none := (hp3 p0 (by simp)).mp (by rw [hp0]; exact hcb0)
            have hprs : ∀ q ∈ pr, q.2 ≠ none := by
              intro q hq hn
              have := (hp3 q (by simp [hq])).mpr hn
              have hq' : q.1 ∈ rest := by rw [← hpr]; exact List.mem_map_of_mem hq
              have := hrest q.1 (by simpa using hq')
              simp_all
            obtain ⟨tx0, un0⟩ := p0
            simp only at hp0 hp0n
            subst hp0 hp0n
            have hund' : undo = pr.filterMap Prod.snd := by
              rw [← hund, hp2]; simp
            unfold disconnectBlock
            rw [hv]
            have hlen : undo.length + 1 = (tx0 :: rest).length := by
              rw [hund', S190BLK_len_pairs pr hprs, ← hpr]; simp
            rw [if_neg (by rw [hlen]; simp)]
            have hz : (tx0 :: rest).zip (none :: undo.map some) = (tx0, none) :: pr := by
              rw [hund', List.zip_cons_cons, ← hpr, S190BLK_zip_pairs pr hprs]
            rw [hz]
            exact hw1

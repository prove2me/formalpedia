-- Prove2me | solution 2 for BitcoinSer.tx_roundtrip
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:53:59.770563+00:00
-- url     : https://prove2.me/submissions/6fc0f373-3774-4ff8-9afc-b3e509b83eb4

import Definitions.Def_BitcoinSer
import Theorems.Thm_BitcoinSer_readLE_leBytes

open BitcoinSer

private theorem leVal_leBytes (k n : Nat) (h : n < 2 ^ (8 * k)) : leVal (leBytes k n) = n := by
  induction k generalizing n with
  | zero => simp at h; subst h; rfl
  | succ k ih =>
    simp only [leBytes, leVal, BitVec.toNat_ofNat, Nat.reducePow]
    have h2 : n / 256 < 2 ^ (8 * k) := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 256 := by
        rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add]
      omega
    rw [ih _ h2]
    all_goals omega

private theorem leVal_lt (l : Bytes) : leVal l < 2 ^ (8 * l.length) := by
  induction l with
  | nil => simp [leVal]
  | cons b rest ih =>
    simp only [leVal, List.length_cons]
    have hb := b.isLt
    have : 2 ^ (8 * (rest.length + 1)) = 2 ^ (8 * rest.length) * 256 := by
      rw [show 8 * (rest.length + 1) = 8 * rest.length + 8 by omega, Nat.pow_add]
    rw [this]
    all_goals omega

private theorem leBytes_leVal (l : Bytes) : leBytes l.length (leVal l) = l := by
  induction l with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons, leBytes, leVal]
    have hb := b.isLt; simp at hb
    have h1 : (b.toNat + 256 * leVal rest) % 256 = b.toNat := by omega
    have h2 : (b.toNat + 256 * leVal rest) / 256 = leVal rest := by omega
    rw [h1, h2, ih, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem readLE_append (l rest : Bytes) (k : Nat) (hk : l.length = k) :
    readLE k (l ++ rest) = some (leVal l, rest) := by
  unfold readLE
  rw [if_neg (by simp; omega), List.take_left' hk, List.drop_left' hk]

/-- A successful fixed-width read determines its input: the bytes are the encoding of the value. -/
private theorem readLE_inv (k : Nat) (s : Bytes) (v : Nat) (rest : Bytes) (h : readLE k s = some (v, rest)) :
    s = leBytes k v ++ rest ∧ v < 2 ^ (8 * k) := by
  unfold readLE at h
  split at h
  · cases h
  · rename_i hlen
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ht : (s.take k).length = k := by simp; omega
    refine ⟨?_, ?_⟩
    · have e := leBytes_leVal (s.take k)
      rw [ht] at e
      rw [e, List.take_append_drop]
    · have := leVal_lt (s.take k); rwa [ht] at this

private theorem ser8_toNat (n : Nat) (h : n < 256) : (BitVec.ofNat 8 (n % 256)).toNat = n := by
  simp [BitVec.toNat_ofNat]; omega

private theorem leBytes_one (x : Nat) : leBytes 1 x = [BitVec.ofNat 8 (x % 256)] := rfl

private theorem compactSize_roundtrip_gen (rc : Bool) (n : Nat) (rest : Bytes) (h : n < 2 ^ 64)
    (hrc : rc = true → n ≤ MAX_SIZE) :
    readCompactSize rc (writeCompactSize n ++ rest) = some (n, rest) := by
  have hm : (rc && decide (MAX_SIZE < n)) = false := by
    cases rc
    · rfl
    · simp; have := hrc rfl; omega
  have hm' : ¬ (rc = true ∧ MAX_SIZE < n) := by
    cases rc
    · simp
    · simp; have := hrc rfl; omega
  unfold writeCompactSize
  by_cases h1 : n < 253
  · rw [if_pos h1]
    simp only [ser8, leBytes_one, List.cons_append, List.nil_append, readCompactSize]
    rw [ser8_toNat n (by omega)]
    simp [h1, hm]
  · rw [if_neg h1]
    by_cases h2 : n ≤ 0xffff
    · rw [if_pos h2]
      simp only [ser8, ser16, leBytes_one, List.cons_append, List.nil_append, readCompactSize]
      rw [ser8_toNat 253 (by omega), readLE_leBytes 2 n rest (by rw [show (2:Nat)^(8*2) = 65536 from rfl]; omega)]
      simp [h1, hm]
    · rw [if_neg h2]
      by_cases h3 : n ≤ 0xffffffff
      · rw [if_pos h3]
        simp only [ser8, ser32, leBytes_one, List.cons_append, List.nil_append, readCompactSize]
        rw [ser8_toNat 254 (by omega), readLE_leBytes 4 n rest (by rw [show (2:Nat)^(8*4) = 4294967296 from rfl]; omega)]
        simp [hm]
        rw [if_neg (show ¬ n < 65536 by omega)]
        dsimp only
        rw [if_neg hm']
      · rw [if_neg h3]
        simp only [ser8, ser64, leBytes_one, List.cons_append, List.nil_append, readCompactSize]
        rw [ser8_toNat 255 (by omega), readLE_leBytes 8 n rest (by rw [show (2:Nat)^(8*8) = 18446744073709551616 from rfl]; omega)]
        simp [hm]
        rw [if_neg (show ¬ n < 4294967296 by omega)]
        dsimp only
        rw [if_neg hm']

/-- The multi-byte tail of `ReadCompactSize`: a successful read fixes the bytes and the range. -/
private theorem tail_inv (rc : Bool) (k lo : Nat) (tl : Bytes) (n : Nat) (rest : Bytes)
    (h : (match (match readLE k tl with
                 | some (v, r) => if v < lo then none else some (v, r)
                 | none => none) with
          | some (v, r) => if (rc && decide (MAX_SIZE < v)) = true then none else some (v, r)
          | none => none) = some (n, rest)) :
    tl = leBytes k n ++ rest ∧ lo ≤ n ∧ n < 2 ^ (8 * k) ∧ (rc = true → n ≤ MAX_SIZE) := by
  cases hv : readLE k tl with
  | none => rw [hv] at h; simp at h
  | some p =>
    rw [hv] at h
    obtain ⟨v, r⟩ := p
    dsimp only at h
    by_cases hlo : v < lo
    · rw [if_pos hlo] at h; simp at h
    · rw [if_neg hlo] at h
      dsimp only at h
      split at h
      · cases h
      · rename_i hrc
        cases h
        have := readLE_inv k tl n rest hv
        refine ⟨this.1, by omega, this.2, fun hr => ?_⟩
        subst hr; simp at hrc; omega

private theorem compactSize_inv (rc : Bool) (b : Bytes) (n : Nat) (rest : Bytes)
    (h : readCompactSize rc b = some (n, rest)) :
    b = writeCompactSize n ++ rest ∧ n < 2 ^ 64 ∧ (rc = true → n ≤ MAX_SIZE) := by
  cases b with
  | nil => simp [readCompactSize] at h
  | cons ch tl =>
    unfold readCompactSize at h
    dsimp only at h
    have hch := ch.isLt
    by_cases hc1 : ch.toNat < 253
    · rw [if_pos hc1] at h
      dsimp only at h
      split at h
      · cases h
      · rename_i hrc
        cases h
        refine ⟨?_, by omega, fun hr => ?_⟩
        · unfold writeCompactSize
          rw [if_pos hc1]
          simp only [ser8, leBytes_one, List.cons_append, List.nil_append]
          rw [Nat.mod_eq_of_lt (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
        · subst hr; simp at hrc; omega
    · rw [if_neg hc1] at h
      by_cases hc2 : ch.toNat = 253
      · rw [if_pos hc2] at h
        obtain ⟨e, hlo, hlt, hrc⟩ := tail_inv rc 2 253 tl n rest h
        refine ⟨?_, by omega, hrc⟩
        unfold writeCompactSize
        rw [if_neg (by omega), if_pos (by rw [show (2:Nat)^(8*2) = 65536 from rfl] at hlt; omega)]
        simp only [ser8, ser16, leBytes_one, List.cons_append, List.nil_append, List.append_assoc]
        rw [e, show (BitVec.ofNat 8 (253 % 256)) = ch by rw [← hc2, Nat.mod_eq_of_lt (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]]
      · rw [if_neg hc2] at h
        by_cases hc3 : ch.toNat = 254
        · rw [if_pos hc3] at h
          obtain ⟨e, hlo, hlt, hrc⟩ := tail_inv rc 4 0x10000 tl n rest h
          rw [show (2:Nat)^(8*4) = 4294967296 from rfl] at hlt
          refine ⟨?_, by omega, hrc⟩
          unfold writeCompactSize
          rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          simp only [ser8, ser32, leBytes_one, List.cons_append, List.nil_append, List.append_assoc]
          rw [e, show (BitVec.ofNat 8 (254 % 256)) = ch by rw [← hc3, Nat.mod_eq_of_lt (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]]
        · rw [if_neg hc3] at h
          obtain ⟨e, hlo, hlt, hrc⟩ := tail_inv rc 8 0x100000000 tl n rest h
          rw [show (2:Nat)^(8*8) = 18446744073709551616 from rfl] at hlt
          refine ⟨?_, by omega, hrc⟩
          unfold writeCompactSize
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          simp only [ser8, ser64, leBytes_one, List.cons_append, List.nil_append, List.append_assoc]
          have hc4 : ch.toNat = 255 := by omega
          rw [e, show (BitVec.ofNat 8 (255 % 256)) = ch by rw [← hc4, Nat.mod_eq_of_lt (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]]

private theorem compactSize_roundtrip_rc (n : Nat) (rest : Bytes) (h : n ≤ MAX_SIZE) :
    readCompactSize true (writeCompactSize n ++ rest) = some (n, rest) :=
  compactSize_roundtrip_gen true n rest (by unfold MAX_SIZE at h; omega) (fun _ => h)

private theorem readN_flatMap {α : Type} (f : α → Bytes) (g : Bytes → Option (α × Bytes)) :
    ∀ (l : List α) (rest : Bytes), (∀ x ∈ l, ∀ r, g (f x ++ r) = some (x, r)) →
      readN g l.length (l.flatMap f ++ rest) = some (l, rest)
  | [], rest, _ => by simp [readN]
  | x :: xs, rest, hg => by
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readN]
    rw [hg x (List.mem_cons_self ..)]
    dsimp only
    rw [readN_flatMap f g xs rest (fun y hy => hg y (List.mem_cons_of_mem _ hy))]

/-- Reading a serialized vector yields it, element-wise reader permitting. -/
private theorem readList_serList {α : Type} (f : α → Bytes) (g : Bytes → Option (α × Bytes))
    (l : List α) (rest : Bytes) (hg : ∀ x ∈ l, ∀ r, g (f x ++ r) = some (x, r))
    (hl : l.length ≤ MAX_SIZE) : readList g (serList f l ++ rest) = some (l, rest) := by
  unfold readList serList
  rw [List.append_assoc, compactSize_roundtrip_rc _ _ hl]
  exact readN_flatMap f g l rest hg

private theorem readBytes_serBytes (b rest : Bytes) (hb : b.length ≤ MAX_SIZE) :
    readBytes (serBytes b ++ rest) = some (b, rest) := by
  unfold readBytes serBytes
  rw [List.append_assoc, compactSize_roundtrip_rc _ _ hb]
  dsimp only
  rw [if_neg (by rw [List.length_append]; omega), List.take_left, List.drop_left]

private theorem readHash_append (h rest : Bytes) (hh : h.length = 32) :
    readHash (h ++ rest) = some (h, rest) := by
  unfold readHash
  rw [if_neg (by rw [List.length_append]; omega), List.take_left' hh, List.drop_left' hh]

private theorem readInt64_serInt64 (n : Int) (rest : Bytes) (h1 : -(2 ^ 63) ≤ n) (h2 : n < 2 ^ 63) :
    readInt64 (serInt64 n ++ rest) = some (n, rest) := by
  unfold readInt64 serInt64
  rw [BitcoinSer.readLE_leBytes 8 _ rest (by
    have := Int.emod_lt_of_pos n (show (0:Int) < 2 ^ 64 by decide)
    have h0 := Int.emod_nonneg n (show (2:Int) ^ 64 ≠ 0 by decide)
    rw [show (2:Nat) ^ (8 * 8) = 2 ^ 64 from rfl]; omega)]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
  have h0 := Int.emod_nonneg n (show (2:Int) ^ 64 ≠ 0 by decide)
  have hlt := Int.emod_lt_of_pos n (show (0:Int) < 2 ^ 64 by decide)
  rw [Int.toNat_of_nonneg h0]
  by_cases hn : 0 ≤ n
  · rw [Int.emod_eq_of_lt hn (by omega), if_pos (by omega)]
    all_goals omega
  · have : n % 2 ^ 64 = n + 2 ^ 64 := by omega
    rw [this, if_neg (by omega)]
    all_goals omega

private theorem readInt32_serInt32 (n : Int) (rest : Bytes) (h1 : -(2 ^ 31) ≤ n) (h2 : n < 2 ^ 31) :
    readInt32 (serInt32 n ++ rest) = some (n, rest) := by
  unfold readInt32 serInt32
  rw [BitcoinSer.readLE_leBytes 4 _ rest (by
    have := Int.emod_lt_of_pos n (show (0:Int) < 2 ^ 32 by decide)
    have h0 := Int.emod_nonneg n (show (2:Int) ^ 32 ≠ 0 by decide)
    rw [show (2:Nat) ^ (8 * 4) = 2 ^ 32 from rfl]; omega)]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
  have h0 := Int.emod_nonneg n (show (2:Int) ^ 32 ≠ 0 by decide)
  have hlt := Int.emod_lt_of_pos n (show (0:Int) < 2 ^ 32 by decide)
  rw [Int.toNat_of_nonneg h0]
  by_cases hn : 0 ≤ n
  · rw [Int.emod_eq_of_lt hn (by omega), if_pos (by omega)]
    all_goals omega
  · have : n % 2 ^ 32 = n + 2 ^ 32 := by omega
    rw [this, if_neg (by omega)]
    all_goals omega

private theorem readOutPoint_ser (o : OutPoint) (rest : Bytes) (hw : o.wf) :
    readOutPoint (serOutPoint o ++ rest) = some (o, rest) := by
  obtain ⟨hh, hn⟩ := hw
  unfold readOutPoint serOutPoint
  rw [List.append_assoc, readHash_append _ _ hh]; dsimp only
  simp only [ser32]
  rw [BitcoinSer.readLE_leBytes 4 _ _ (by rw [show (2:Nat)^(8*4) = 2^32 from rfl]; exact hn)]

private theorem readTxIn_ser (i : TxIn) (rest : Bytes) (hw : i.wf) :
    readTxIn (serTxIn i ++ rest) = some ({ i with witness := [] }, rest) := by
  obtain ⟨hp, hs, hq, _, _⟩ := hw
  unfold readTxIn serTxIn
  simp only [List.append_assoc]
  rw [readOutPoint_ser _ _ hp]; dsimp only
  rw [readBytes_serBytes _ _ hs]; dsimp only
  simp only [ser32]
  rw [BitcoinSer.readLE_leBytes 4 _ _ (by rw [show (2:Nat)^(8*4) = 2^32 from rfl]; exact hq)]

private theorem readTxOut_ser (o : TxOut) (rest : Bytes) (hw : o.wf) :
    readTxOut (serTxOut o ++ rest) = some (o, rest) := by
  obtain ⟨h1, h2, hs⟩ := hw
  unfold readTxOut serTxOut
  rw [List.append_assoc, readInt64_serInt64 _ _ h1 h2]; dsimp only
  rw [readBytes_serBytes _ _ hs]

private theorem readList_vin (l : List TxIn) (rest : Bytes) (hl : l.length ≤ MAX_SIZE) (hw : ∀ i ∈ l, i.wf) :
    readList readTxIn (serList serTxIn l ++ rest) = some (l.map (fun i => { i with witness := [] }), rest) := by
  unfold readList serList
  rw [List.append_assoc, compactSize_roundtrip_rc _ _ hl]
  dsimp only
  induction l generalizing rest with
  | nil => simp [readN]
  | cons i is ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readN, List.map_cons]
    rw [readTxIn_ser i _ (hw i (List.mem_cons_self ..))]
    dsimp only
    rw [ih rest (by simp at hl; omega) (fun j hj => hw j (List.mem_cons_of_mem _ hj))]

private theorem readList_vout (l : List TxOut) (rest : Bytes) (hl : l.length ≤ MAX_SIZE) (hw : ∀ o ∈ l, o.wf) :
    readList readTxOut (serList serTxOut l ++ rest) = some (l, rest) := by
  unfold readList serList
  rw [List.append_assoc, compactSize_roundtrip_rc _ _ hl]
  dsimp only
  induction l generalizing rest with
  | nil => simp [readN]
  | cons o os ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readN]
    rw [readTxOut_ser o _ (hw o (List.mem_cons_self ..))]
    dsimp only
    rw [ih rest (by simp at hl; omega) (fun j hj => hw j (List.mem_cons_of_mem _ hj))]

private theorem readList_bytes (l : List Bytes) (rest : Bytes) (hl : l.length ≤ MAX_SIZE)
    (hw : ∀ w ∈ l, w.length ≤ MAX_SIZE) :
    readList readBytes (serList serBytes l ++ rest) = some (l, rest) :=
  readList_serList serBytes readBytes l rest (fun x hx r => readBytes_serBytes x r (hw x hx)) hl

private theorem readWitnesses_ser :
    ∀ (vin : List TxIn) (rest : Bytes), (∀ i ∈ vin, i.wf) →
      readN (readList readBytes) vin.length (vin.flatMap (fun i => serList serBytes i.witness) ++ rest) =
        some (vin.map (·.witness), rest)
  | [], rest, _ => by simp [readN]
  | i :: is, rest, hw => by
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readN, List.map_cons]
    have hi := hw i (List.mem_cons_self ..)
    rw [readList_bytes _ _ hi.2.2.2.1 hi.2.2.2.2]
    dsimp only
    rw [readWitnesses_ser is rest (fun j hj => hw j (List.mem_cons_of_mem _ hj))]

private theorem attachWitness_map (vin : List TxIn) :
    attachWitness (vin.map fun i => { i with witness := [] }) (vin.map (·.witness)) = vin := by
  induction vin with
  | nil => rfl
  | cons i is ih => simp [attachWitness, ih]

private theorem strip_of_no_witness (vin : List TxIn) (h : (vin.any fun i => !i.witness.isEmpty) = false) :
    vin.map (fun i => { i with witness := [] }) = vin := by
  induction vin with
  | nil => rfl
  | cons i is ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at h
    obtain ⟨hi, hs⟩ := h
    simp only [List.map_cons, ih hs]
    cases i; simp only at hi; subst hi; rfl

private theorem serTx_basic (aw : Bool) (tx : Tx) (h : (aw && tx.hasWitness) = false) :
    serTx aw tx = ser32 tx.version ++ serList serTxIn tx.vin ++ serList serTxOut tx.vout ++ ser32 tx.nLockTime := by
  simp [serTx, h]

private theorem serTx_ext (tx : Tx) (h : tx.hasWitness = true) :
    serTx true tx = ser32 tx.version ++ [0, 1] ++ serList serTxIn tx.vin ++ serList serTxOut tx.vout ++
      tx.vin.flatMap (fun i => serList serBytes i.witness) ++ ser32 tx.nLockTime := by
  simp [serTx, h]; rfl

private theorem readTx_basic (aw : Bool) (tx : Tx) (rest : Bytes) (hw : tx.wf) (hv : aw = true → tx.vin ≠ []) :
    readTx aw (ser32 tx.version ++ serList serTxIn tx.vin ++ serList serTxOut tx.vout ++ ser32 tx.nLockTime ++ rest) =
      some (tx.stripWitness, rest) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  unfold readTx
  simp only [List.append_assoc, ser32]
  rw [BitcoinSer.readLE_leBytes 4 _ _ (by rw [show (2:Nat)^(8*4) = 2^32 from rfl]; exact h1)]; dsimp only
  rw [readList_vin _ _ h3 h5]; dsimp only
  have hne : ((tx.vin.map fun i => { i with witness := [] }).isEmpty && aw) = false := by
    cases aw
    · simp
    · cases hvin : tx.vin with
      | nil => exact absurd hvin (hv rfl)
      | cons _ _ => rfl
  rw [hne]
  simp only [Bool.false_eq_true, ite_false]
  rw [readList_vout _ _ h4 h6]; dsimp only
  simp only [Nat.zero_mod, Nat.zero_ne_one, decide_false, Bool.false_and, Bool.false_eq_true, ite_false,
    ne_eq, not_true_eq_false]
  rw [BitcoinSer.readLE_leBytes 4 _ _ (by rw [show (2:Nat)^(8*4) = 2^32 from rfl]; exact h2)]
  rfl

private theorem readTx_ext (tx : Tx) (rest : Bytes) (hw : tx.wf) (hwit : tx.hasWitness = true) :
    readTx true (ser32 tx.version ++ [0, 1] ++ serList serTxIn tx.vin ++ serList serTxOut tx.vout ++
      tx.vin.flatMap (fun i => serList serBytes i.witness) ++ ser32 tx.nLockTime ++ rest) = some (tx, rest) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  unfold readTx
  simp only [List.append_assoc, ser32, List.cons_append, List.nil_append]
  rw [BitcoinSer.readLE_leBytes 4 _ _ (by rw [show (2:Nat)^(8*4) = 2^32 from rfl]; exact h1)]; dsimp only
  -- the dummy: `readList` of the byte `0x00` yields the empty vector
  have hdummy : ∀ s, readList readTxIn ((0 : Byte) :: s) = some ([], s) := by
    intro s; simp [readList, readCompactSize, readN]
  rw [hdummy]; dsimp only
  simp only [List.isEmpty_nil, Bool.true_and, ite_true, show (1 : Byte).toNat = 1 from rfl, Nat.one_ne_zero,
    not_false_eq_true]
  rw [readList_vin _ _ h3 h5]; dsimp only
  rw [readList_vout _ _ h4 h6]; dsimp only
  simp only [ne_eq, Nat.one_ne_zero, not_false_eq_true, ite_true]
  (try dsimp only)
  simp only [Nat.one_mod, decide_true, Bool.true_and, ite_true, List.length_map, readWitnesses]
  rw [readWitnesses_ser _ _ h5]; dsimp only
  rw [attachWitness_map]
  have hw' : ({ version := 0, vin := tx.vin, vout := [], nLockTime := 0 } : Tx).hasWitness = true := hwit
  simp only [hw', ite_true, Nat.sub_self, ne_eq, not_true_eq_false, ite_false]
  rw [BitcoinSer.readLE_leBytes 4 _ _ (by rw [show (2:Nat)^(8*4) = 2^32 from rfl]; exact h2)]

theorem solution (aw : Bool) (tx : Tx) (rest : Bytes) (hw : tx.wf)
    (hv : aw = true → tx.vin ≠ []) :
    BitcoinSer.readTx aw (BitcoinSer.serTx aw tx ++ rest) =
      some (if aw then tx else tx.stripWitness, rest) := by
  by_cases hb : (aw && tx.hasWitness) = false
  · rw [serTx_basic aw tx hb, readTx_basic aw tx rest hw hv]
    cases aw with
    | false => rfl
    | true =>
      simp only [Bool.true_and] at hb
      simp only [ite_true, Option.some.injEq, Prod.mk.injEq, and_true]
      unfold Tx.stripWitness
      rw [strip_of_no_witness _ hb]
  · simp only [Bool.and_eq_false_iff, not_or, Bool.not_eq_false] at hb
    obtain ⟨rfl, hwit⟩ := hb
    rw [serTx_ext tx hwit, readTx_ext tx rest hw hwit]
    rfl

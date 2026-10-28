-- Prove2me | solution 1 for BitcoinSer.serBlock_injective
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:08:53.975011+00:00
-- url     : https://prove2.me/submissions/9476fc46-5da1-428c-850b-094e706a17a7

import Definitions.Def_BitcoinSer

namespace BR_Inj
open BitcoinSer

theorem BR_len (k n : Nat) : (leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

theorem BR_val (k n : Nat) (h : n < 2 ^ (8 * k)) : leVal (leBytes k n) = n := by
  induction k generalizing n with
  | zero => simp at h; subst h; rfl
  | succ k ih =>
    simp only [leBytes, leVal]
    have : n / 256 < 2 ^ (8 * k) := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      have : 2 ^ (8 * (k+1)) = 2 ^ (8*k) * 256 := by rw [show 8*(k+1) = 8*k+8 by omega, Nat.pow_add]
      omega
    rw [ih _ this]
    simp [BitVec.toNat_ofNat]
    omega

theorem BR_read (k n : Nat) (rest : Bytes) (h : n < 2 ^ (8 * k)) :
    readLE k (leBytes k n ++ rest) = some (n, rest) := by
  simp [readLE, BR_len, BR_val k n h]

theorem BR_read32 (n : Nat) (rest : Bytes) (h : n < 2 ^ 32) :
    readLE 4 (ser32 n ++ rest) = some (n, rest) := BR_read 4 n rest h

theorem BR_hash (p rest : Bytes) (h : p.length = 32) :
    readHash (p ++ rest) = some (p, rest) := by
  simp [readHash, h]

theorem BR_int64 (v : Int) (rest : Bytes) (h1 : -(2 ^ 63) ≤ v) (h2 : v < 2 ^ 63) :
    readInt64 (serInt64 v ++ rest) = some (v, rest) := by
  have hnn : 0 ≤ v % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have hm : (((v % 2 ^ 64).toNat : Nat) : Int) = v % 2 ^ 64 := Int.toNat_of_nonneg hnn
  have hlt : (v % 2 ^ 64).toNat < 2 ^ (8 * 8) := by omega
  simp only [readInt64, serInt64, BR_read 8 _ rest hlt, Option.map_some]
  congr 2
  split <;> omega

theorem BR_csrt (rc : Bool) (n : Nat) (rest : Bytes) (h : n < 2 ^ 64) (hr : rc = true → n ≤ MAX_SIZE) :
    readCompactSize rc (writeCompactSize n ++ rest) = some (n, rest) := by
  unfold writeCompactSize
  by_cases h1 : n < 253
  · simp only [h1, if_true, ser8, leBytes, List.cons_append, List.nil_append, readCompactSize]
    have : (BitVec.ofNat 8 (n % 256)).toNat = n := by simp [BitVec.toNat_ofNat]; omega
    simp only [this, h1, if_true]
    cases rc <;> simp_all
  by_cases h2 : n ≤ 0xffff
  · simp only [h1, h2, if_true, if_false, ser8, ser16, leBytes, List.cons_append, List.nil_append,
      readCompactSize]
    have := BR_read 2 n rest (by omega)
    simp only [leBytes, List.cons_append, List.nil_append] at this
    rw [this]
    have e : ¬ n < 253 := h1
    simp only [e, if_false]
    have hm : rc = true → ¬ MAX_SIZE < n := fun hh => Nat.not_lt.2 (hr hh)
    cases rc <;> simp_all
  by_cases h3 : n ≤ 0xffffffff
  · simp only [h1, h2, h3, if_true, if_false, ser8, ser32, leBytes, List.cons_append, List.nil_append,
      readCompactSize]
    have := BR_read 4 n rest (by omega)
    simp only [leBytes, List.cons_append, List.nil_append] at this
    rw [this]
    have e : ¬ n < 0x10000 := by omega
    simp only [e, if_false]
    have hm : rc = true → ¬ MAX_SIZE < n := fun hh => Nat.not_lt.2 (hr hh)
    cases rc <;> simp_all
  · simp only [h1, h2, h3, if_false, ser8, ser64, leBytes, List.cons_append, List.nil_append,
      readCompactSize]
    have := BR_read 8 n rest (by omega)
    simp only [leBytes, List.cons_append, List.nil_append] at this
    rw [this]
    have e : ¬ n < 0x100000000 := by omega
    simp only [e, if_false]
    have hm : rc = true → ¬ MAX_SIZE < n := fun hh => Nat.not_lt.2 (hr hh)
    cases rc <;> simp_all

theorem BR_cs (n : Nat) (rest : Bytes) (h : n ≤ MAX_SIZE) :
    readCompactSize true (writeCompactSize n ++ rest) = some (n, rest) :=
  BR_csrt true n rest (by unfold MAX_SIZE at h; omega) (fun _ => h)

theorem BR_readN {α β : Type} (f : Bytes → Option (α × Bytes)) (g : β → Bytes) (k : β → α)
    (l : List β) (rest : Bytes) (hf : ∀ x ∈ l, ∀ r, f (g x ++ r) = some (k x, r)) :
    readN f l.length (l.flatMap g ++ rest) = some (l.map k, rest) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readN,
      hf x (by simp), List.map_cons]
    rw [ih (fun y hy r => hf y (by simp [hy]) r)]

theorem BR_readList {α β : Type} (f : Bytes → Option (α × Bytes)) (g : β → Bytes) (k : β → α)
    (l : List β) (rest : Bytes) (hl : l.length ≤ MAX_SIZE)
    (hf : ∀ x ∈ l, ∀ r, f (g x ++ r) = some (k x, r)) :
    readList f (serList g l ++ rest) = some (l.map k, rest) := by
  simp only [readList, serList, List.append_assoc, BR_cs _ _ hl]
  exact BR_readN f g k l rest hf

theorem BR_bytes (b rest : Bytes) (h : b.length ≤ MAX_SIZE) :
    readBytes (serBytes b ++ rest) = some (b, rest) := by
  simp [readBytes, serBytes, BR_cs _ _ h]

theorem BR_txin (i : TxIn) (rest : Bytes) (h : i.wf) :
    readTxIn (serTxIn i ++ rest) = some ({ i with witness := [] }, rest) := by
  obtain ⟨⟨h1, h2⟩, h3, h4, -, -⟩ := h
  simp only [readTxIn, readOutPoint, serTxIn, serOutPoint, List.append_assoc, BR_hash _ _ h1,
    BR_read32 _ _ h2, BR_bytes _ _ h3, BR_read32 _ _ h4]

theorem BR_txout (o : TxOut) (rest : Bytes) (h : o.wf) :
    readTxOut (serTxOut o ++ rest) = some (o, rest) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [readTxOut, serTxOut, List.append_assoc, BR_int64 _ _ h1 h2, BR_bytes _ _ h3]

theorem BR_attach (l : List TxIn) :
    attachWitness (l.map fun i => { i with witness := [] }) (l.map (·.witness)) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [attachWitness, ih]

theorem BR_nowit (l : List TxIn) (h : ∀ i ∈ l, i.witness = []) :
    (l.map fun i => { i with witness := [] }) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    simp only [List.map_cons, ih (fun y hy => h y (by simp [hy]))]
    cases x; simp_all

theorem BR_txrt (aw : Bool) (tx : Tx) (rest : Bytes) (hw : tx.wf)
    (hv : aw = true → tx.vin ≠ []) :
    BitcoinSer.readTx aw (BitcoinSer.serTx aw tx ++ rest) =
      some (if aw then tx else tx.stripWitness, rest) := by
  obtain ⟨hv1, hv2, hv3, hv4, hv5, hv6⟩ := hw
  have hin : ∀ r, readList readTxIn (serList serTxIn tx.vin ++ r) =
      some (tx.vin.map fun i => { i with witness := [] }, r) := fun r =>
    BR_readList _ _ _ _ _ hv3 (fun i hi r => BR_txin i r (hv5 i hi))
  have hout : ∀ r, readList readTxOut (serList serTxOut tx.vout ++ r) = some (tx.vout, r) := by
    intro r
    have := BR_readList readTxOut serTxOut (fun o => o) tx.vout r hv4
      (fun o ho r => BR_txout o r (hv6 o ho))
    simpa using this
  have hwit : ∀ r, readWitnesses tx.vin.length
      (tx.vin.flatMap (fun i => serList serBytes i.witness) ++ r) =
      some (tx.vin.map (·.witness), r) := by
    intro r
    refine BR_readN _ _ _ _ _ (fun i hi r => ?_)
    obtain ⟨-, -, -, h1, h2⟩ := hv5 i hi
    have := BR_readList readBytes serBytes (fun b => b) i.witness r h1
      (fun b hb r => BR_bytes b r (h2 b hb))
    simpa using this
  have hl4 := fun r => BR_read32 _ r hv2
  have hv4' := fun r => BR_read32 _ r hv1
  cases aw with
  | false =>
    simp [serTx, readTx, List.append_assoc, hin, hout, hl4, hv4', Tx.stripWitness]
  | true =>
    cases hW : tx.hasWitness with
    | false =>
      have hne := hv rfl
      have hall : ∀ i ∈ tx.vin, i.witness = [] := by
        simpa [Tx.hasWitness] using hW
      have e : serTx true tx ++ rest = ser32 tx.version ++ (serList serTxIn tx.vin ++
          (serList serTxOut tx.vout ++ (ser32 tx.nLockTime ++ rest))) := by
        simp [serTx, hW]
      rw [e]
      simp only [readTx, hv4', hin, hout, BR_nowit _ hall]
      simp [hne, hl4]
    | true =>
      have h0 : ∀ r, readList readTxIn (writeCompactSize 0 ++ r) = some ([], r) := fun r => by
        simpa [serList] using BR_readList readTxIn serTxIn id [] r (by simp [MAX_SIZE])
          (by simp)
      have hW' : Tx.hasWitness ⟨0, tx.vin, [], 0⟩ = true := hW
      have e : serTx true tx ++ rest = ser32 tx.version ++ (writeCompactSize 0 ++ (1#8 ::
          (serList serTxIn tx.vin ++ (serList serTxOut tx.vout ++
          (tx.vin.flatMap (fun i => serList serBytes i.witness) ++ (ser32 tx.nLockTime ++ rest)))))) := by
        simp [serTx, hW, ser8, leBytes]
      rw [e]
      simp only [readTx, hv4', h0]
      simp only [List.isEmpty_nil, Bool.true_and, if_true, BitVec.toNat_ofNat]
      simp only [hin, hout]
      simp [hwit, BR_attach, hW', hl4]

theorem BR_int32 (v : Int) (rest : Bytes) (h1 : -(2 ^ 31) ≤ v) (h2 : v < 2 ^ 31) :
    readInt32 (serInt32 v ++ rest) = some (v, rest) := by
  have hnn : 0 ≤ v % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have hm : (((v % 2 ^ 32).toNat : Nat) : Int) = v % 2 ^ 32 := Int.toNat_of_nonneg hnn
  have hlt : (v % 2 ^ 32).toNat < 2 ^ (8 * 4) := by omega
  simp only [readInt32, serInt32, BR_read 4 _ rest hlt, Option.map_some]
  congr 2
  split <;> omega

theorem BR_hdrrt (h : Header) (rest : Bytes) (hw : h.wf) :
    BitcoinSer.readHeader (BitcoinSer.serHeader h ++ rest) = some (h, rest) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hw
  simp only [readHeader, serHeader, List.append_assoc, BR_int32 _ _ h1 h2,
    BR_hash _ _ h3, BR_hash _ _ h4, BR_read32 _ _ h5,
    BR_read32 _ _ h6, BR_read32 _ _ h7]

theorem BR_vin (tx : Tx) (h : tx.vin ≠ [] ∨ tx.hasWitness = true) : tx.vin ≠ [] := by
  rcases h with h | h
  · exact h
  · intro e; simp [Tx.hasWitness, e] at h

theorem BR_blkrt (aw : Bool) (b : Block) (rest : Bytes) (hw : b.wf) :
    BitcoinSer.readBlock aw (BitcoinSer.serBlock aw b ++ rest) =
      some (⟨b.header, b.vtx.map (fun tx => if aw then tx else tx.stripWitness)⟩, rest) := by
  obtain ⟨hh, hl, ht⟩ := hw
  simp only [readBlock, serBlock, List.append_assoc, BR_hdrrt _ _ hh,
    BR_readList (readTx aw) (serTx aw) (fun tx => if aw then tx else tx.stripWitness)
      b.vtx rest hl (fun tx htx r => BR_txrt aw tx r (ht tx htx).1
        (fun _ => BR_vin tx (ht tx htx).2))]

end BR_Inj

open BitcoinSer in
theorem solution (b₁ b₂ : Block) (h₁ : b₁.wf) (h₂ : b₂.wf)
    (h : BitcoinSer.serBlock true b₁ = BitcoinSer.serBlock true b₂) : b₁ = b₂ := by
  have e1 := BR_Inj.BR_blkrt true b₁ [] h₁
  have e2 := BR_Inj.BR_blkrt true b₂ [] h₂
  rw [h, e2] at e1
  simp only [if_true, List.map_id', Option.some.injEq, Prod.mk.injEq, and_true] at e1
  cases b₁; cases b₂
  simpa using e1.symm


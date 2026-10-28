-- Prove2me | solution 1 for BitcoinSer.serTx_strip
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:03:28.203987+00:00
-- url     : https://prove2.me/submissions/f62ba507-8db5-4b79-9b81-7ceb8a43cdda

import Definitions.Def_BitcoinSer
open BitcoinSer

theorem B_len (k n : Nat) : (leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

theorem B_sha (m : Bytes) : (sha256 m).length = 32 := by
  simp [sha256, be32Bytes, beBytes, B_len]

theorem B_h160 (m : Bytes) : (hash160 m).length = 20 := by
  simp [hash160, ripemd160, le32Bytes, B_len]

theorem B_hdr (h : Header) (hw : h.wf) : (serHeader h).length = 80 := by
  obtain ⟨-, -, h1, h2, -⟩ := hw
  simp [serHeader, serInt32, ser32, B_len, h1, h2]

theorem B_val (k n : Nat) (h : n < 2 ^ (8 * k)) : leVal (leBytes k n) = n := by
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

theorem B_read (k n : Nat) (rest : Bytes) (h : n < 2 ^ (8 * k)) :
    readLE k (leBytes k n ++ rest) = some (n, rest) := by
  simp [readLE, B_len, B_val k n h]

theorem B_strip (tx : Tx) : serTx false tx = serTx false tx.stripWitness := by
  simp [serTx, Tx.stripWitness, serList, serTxIn, List.flatMap_map]
  congr 1; funext a; simp [serTxIn]

theorem B_txid (tx : Tx) : txid tx = txid tx.stripWitness := by
  simp only [txid]; rw [← B_strip]

theorem B_w (tx : Tx) (h : tx.hasWitness = false) :
    serTx true tx = serTx false tx ∧
      txWeight tx = WITNESS_SCALE_FACTOR * (serTx false tx).length := by
  have e : serTx true tx = serTx false tx := by simp [serTx, h]
  refine ⟨e, ?_⟩
  simp only [txWeight, e, WITNESS_SCALE_FACTOR]; omega

open BitcoinSer in
theorem solution (tx : Tx) : BitcoinSer.serTx false tx = BitcoinSer.serTx false tx.stripWitness :=
  B_strip tx

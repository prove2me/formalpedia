-- Prove2me | solution 1 for BitcoinSig.sigHashLegacy_skeleton
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:25:09.477508+00:00
-- url     : https://prove2.me/submissions/e1e52eb3-f0bc-4e71-99a7-36f4156def4c

import Definitions.Def_BitcoinSig

namespace BS_7d18
open BitcoinSig BitcoinSer

theorem BS_getD (l l' : List TxIn) (k : Nat) (d : TxIn)
    (h : l'.map (fun i => (i.prevout, i.nSequence)) = l.map (fun i => (i.prevout, i.nSequence))) :
    (l'.getD k d).prevout = (l.getD k d).prevout ∧
      (l'.getD k d).nSequence = (l.getD k d).nSequence := by
  induction l generalizing l' k with
  | nil => cases l' <;> simp_all
  | cons x xs ih =>
    cases l' with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      cases k with
      | zero => simp [h.1.1, h.1.2]
      | succ k => simpa using ih ys k h.2

theorem BS_in (scriptCode : Bytes) (tx tx' : Tx) (nIn : Nat) (a s n_ : Bool)
    (h : tx'.vin.map (fun i => (i.prevout, i.nSequence)) = tx.vin.map (fun i => (i.prevout, i.nSequence))) :
    serSigInput tx' scriptCode nIn a s n_ = serSigInput tx scriptCode nIn a s n_ := by
  funext k
  have e := BS_getD tx.vin tx'.vin (if a then nIn else k) ⟨⟨[], 0⟩, [], 0, []⟩ h
  simp only [serSigInput, e.1, e.2]

end BS_7d18

open BitcoinSig BitcoinSer in
theorem solution (scriptCode : Bytes) (tx tx' : Tx) (nIn hashType : Nat)
    (h : BitcoinSig.sameSkeleton tx tx') :
    BitcoinSig.sigHashLegacy scriptCode tx' nIn hashType = BitcoinSig.sigHashLegacy scriptCode tx nIn hashType := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hl : tx'.vin.length = tx.vin.length := by
    have := congrArg List.length h4; simpa using this
  have hs : serSigTx tx' scriptCode nIn hashType = serSigTx tx scriptCode nIn hashType := by
    simp only [serSigTx, h1, h3, hl, BS_7d18.BS_in scriptCode tx tx' nIn _ _ _ h4]
    unfold serSigOutput
    rw [h2]
  simp only [sigHashLegacy, hs, h2]

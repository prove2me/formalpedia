-- Prove2me | solution 1 for BitcoinSig.sigHashWitnessV0_skeleton
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:25:17.517453+00:00
-- url     : https://prove2.me/submissions/08409076-45b7-44cc-a1ad-616bfa84a8fb

import Definitions.Def_BitcoinSig

namespace BS_bc55
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

theorem BS_fm {γ : Type} (g : OutPoint × Nat → List γ) (l l' : List TxIn)
    (h : l'.map (fun i => (i.prevout, i.nSequence)) = l.map (fun i => (i.prevout, i.nSequence))) :
    l'.flatMap (fun i => g (i.prevout, i.nSequence)) = l.flatMap (fun i => g (i.prevout, i.nSequence)) := by
  induction l generalizing l' with
  | nil => cases l' <;> simp_all
  | cons x xs ih =>
    cases l' with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.flatMap_cons, h.1, ih ys h.2]

end BS_bc55

open BitcoinSig BitcoinSer in
theorem solution (scriptCode : Bytes) (tx tx' : Tx) (nIn hashType : Nat) (amount : Int)
    (h : BitcoinSig.sameSkeleton tx tx') :
    BitcoinSig.sigHashWitnessV0 scriptCode tx' nIn hashType amount =
      BitcoinSig.sigHashWitnessV0 scriptCode tx nIn hashType amount := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hp : tx'.vin.flatMap (fun i => serOutPoint i.prevout) =
      tx.vin.flatMap (fun i => serOutPoint i.prevout) :=
    BS_bc55.BS_fm (fun q => serOutPoint q.1) tx.vin tx'.vin h4
  have hq : tx'.vin.flatMap (fun i => ser32 i.nSequence) =
      tx.vin.flatMap (fun i => ser32 i.nSequence) :=
    BS_bc55.BS_fm (fun q => ser32 q.2) tx.vin tx'.vin h4
  have e := BS_bc55.BS_getD tx.vin tx'.vin nIn ⟨⟨[], 0⟩, [], 0, []⟩ h4
  simp only [sigHashWitnessV0, h1, h2, h3, hp, hq, e.1, e.2]

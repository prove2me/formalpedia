-- Prove2me | solution 2 for BitcoinSig.checkSig_base_iff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:56:20.890606+00:00
-- url     : https://prove2.me/submissions/7ee64f87-5333-4233-b0fa-efa9e3297977

import Definitions.Def_BitcoinSig
import Theorems.Thm_BitcoinScript_p2pkh_correct

open BitcoinSig BitcoinSer

private def skel (i : TxIn) : OutPoint × Nat := (i.prevout, i.nSequence)

private def dflt : TxIn := ⟨⟨[], 0⟩, [], 0, []⟩

private theorem getD_prevout (vin : List TxIn) (k : Nat) :
    (vin.getD k dflt).prevout = ((vin.map skel).getD k (skel dflt)).1 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases vin[k]? <;> rfl

private theorem getD_seq (vin : List TxIn) (k : Nat) :
    (vin.getD k dflt).nSequence = ((vin.map skel).getD k (skel dflt)).2 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases vin[k]? <;> rfl

private theorem skel_getD (vin vin' : List TxIn) (hv : vin'.map skel = vin.map skel) (j : Nat) :
    (vin'.getD j dflt).prevout = (vin.getD j dflt).prevout ∧
    (vin'.getD j dflt).nSequence = (vin.getD j dflt).nSequence := by
  constructor
  · rw [getD_prevout, getD_prevout, hv]
  · rw [getD_seq, getD_seq, hv]

private theorem serSigInput_skel (tx tx' : Tx) (h : BitcoinSig.sameSkeleton tx tx') (sc : Bytes) (nIn : Nat)
    (a s z : Bool) :
    serSigInput tx' sc nIn a s z = serSigInput tx sc nIn a s z := by
  obtain ⟨_, _, _, hv⟩ := h
  have hv' : tx'.vin.map skel = tx.vin.map skel := hv
  funext k
  unfold serSigInput
  have e := skel_getD tx.vin tx'.vin hv'
  simp only [show (⟨⟨[], 0⟩, [], 0, []⟩ : TxIn) = dflt from rfl, (e _).1, (e _).2]

private theorem serSigTx_skel (tx tx' : Tx) (h : BitcoinSig.sameSkeleton tx tx') (sc : Bytes) (nIn ht : Nat) :
    serSigTx tx' sc nIn ht = serSigTx tx sc nIn ht := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hlen : tx'.vin.length = tx.vin.length := by
    have := congrArg List.length h4; simpa using this
  have ho : serSigOutput tx' nIn = serSigOutput tx nIn := by
    funext s k; simp [serSigOutput, h2]
  unfold serSigTx
  dsimp only
  rw [h1, h2, h3, hlen, serSigInput_skel tx tx' ⟨h1, h2, h3, h4⟩, ho]

/-- The legacy checker, unfolded: the two encoding checks, a valid key, a non-empty signature whose
last byte is the hash type, and `CPubKey::Verify` on the legacy sighash of the script code with
the signature push deleted. -/
theorem solution (f : SigFlags) (tx : Tx) (nIn : Nat) (amount : Int)
    (scriptCode sig pk : Bytes) :
    BitcoinSig.checkSigPreTapscript f tx nIn amount .base scriptCode sig pk = some true ↔
      BitcoinSig.checkSignatureEncoding f sig = true ∧ BitcoinSig.checkPubKeyEncoding f .base pk = true ∧
      BitcoinSig.pubkeyValid pk = true ∧
      ∃ (sig' : Bytes) (ht : Byte), sig = sig' ++ [ht] ∧
        BitcoinSig.pubkeyVerify pk
          (BitcoinSig.sigHashLegacy (BitcoinSig.findAndDelete scriptCode (BitcoinSig.pushBytes sig)).1 tx nIn ht.toNat)
          sig' = true := by
  unfold checkSigPreTapscript
  by_cases he : checkSignatureEncoding f sig = true
  · by_cases hp : checkPubKeyEncoding f .base pk = true
    · simp only [he, hp, Bool.not_true, Bool.false_eq_true, or_self, ite_false, Option.some.injEq, true_and]
      unfold checkECDSASignature
      by_cases hv : pubkeyValid pk = true
      · simp only [hv, Bool.not_true, Bool.false_eq_true, ite_false, true_and]
        cases hl : sig.getLast? with
        | none =>
          simp only [List.getLast?_eq_none_iff] at hl
          subst hl; simp
        | some ht =>
          simp only [show (SigVersion.base = SigVersion.witnessV0) = False by simp, false_and, ite_false]
          constructor
          · intro hpv
            obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hl
            exact ⟨ys, ht, rfl, by rw [List.dropLast_concat] at hpv; exact hpv⟩
          · rintro ⟨sig', ht', rfl, hpv⟩
            have e : ht' = ht := by
              rw [List.getLast?_append, List.getLast?_singleton] at hl
              simpa using hl
            subst e
            rw [List.dropLast_concat]; exact hpv
      · simp only [Bool.not_eq_true] at hv
        simp [hv]
    · simp only [Bool.not_eq_true] at hp
      simp [hp]
  · simp only [Bool.not_eq_true] at he
    simp [he]

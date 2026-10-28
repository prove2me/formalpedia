-- Prove2me | solution 1 for BitDFT.rewrite_headers_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:36:46.412997+00:00
-- url     : https://prove2.me/submissions/01491f02-e5bf-4356-b1c8-0147805384dc

import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn
import Definitions.Def_BitDFT_RewriteHeaders
import Theorems.Thm_BitDFT_encoded_precision_correct
import Theorems.Thm_BitDFT_header_serialization_correct
import Theorems.Thm_BitDFT_machine_sequence_bound

namespace BitDFT.RewriteCanonical
open IntMul

theorem bin_succ (k z : ℕ) : bin (k+1) z = bin k (z/2) ++ [z.testBit 0] := by
  unfold bin
  rw [List.ofFn_succ',List.concat_eq_append]
  congr 1
  · congr 1
    funext i
    rw [Nat.testBit_div_two]
    congr 1
    simp only [Fin.val_castSucc]
    omega
  · simp

theorem val_append_bit (w : List Bool) (b : Bool) : val (w++[b]) = 2*val w+b.toNat := by
  simp [val,List.foldl_append]

theorem low_bit (z : ℕ) : (z.testBit 0).toNat = z%2 := by
  have h := Nat.mod_lt z (by decide : 0 < 2)
  simp only [Nat.testBit_eq_decide_div_mod_eq,Nat.pow_zero,Nat.div_one]
  by_cases hz : z%2 = 1
  · simp [hz]
  · have h0 : z%2 = 0 := by omega
    simp [h0]

theorem val_bin (k z : ℕ) (hz : z < 2^k) : val (bin k z) = z := by
  induction k generalizing z with
  | zero =>
    have h : z=0 := by simpa using hz
    subst z
    rfl
  | succ k ih =>
    rw [bin_succ,val_append_bit,ih,low_bit]
    · omega
    · have hpow : 2^(k+1) = 2^k*2 := pow_succ _ _
      omega

theorem canonical (n : ℕ) (hn : 1 ≤ n) :
    ∃ tail, bin n.size n = true::tail ∧ tail.length+1=n.size ∧ val (true::tail)=n := by
  have hs : 0 < n.size := Nat.size_pos.mpr (by omega)
  have hb : n.testBit (n.size-1) = true := by
    apply Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt
    · exact Nat.lt_size.mp (by omega)
    · simpa [Nat.sub_add_cancel hs] using Nat.lt_size_self n
  have hval := val_bin n.size n (Nat.lt_size_self n)
  have hlen : (bin n.size n).length = n.size := by simp [bin]
  cases he : bin n.size n with
  | nil => simp [he] at hlen; omega
  | cons b tail =>
    have hhead := congrArg (fun l : List Bool => l[0]?) he
    have hzero : n.size-1-0 = n.size-1 := by omega
    simp [bin,List.getElem?_ofFn,hs,hzero,hb] at hhead
    subst b
    refine ⟨tail,rfl,?_,?_⟩
    · simpa [he] using hlen
    · simpa [he] using hval

end BitDFT.RewriteCanonical


noncomputable section
namespace BitDFT.RewriteHeaders
open IntMul MachineSequence

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem writer_handoff (x tail w v : List Bool) :
    handoff (native NativePrecision.machine) writerControl (NativePrecision.final x tail w v) =
      HeaderSerialization.initial (writerBase x tail w v) (true::tail) v [] := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [handoff,HeaderSerialization.initial,leftCfg,
      HeaderSerialization.firstInitial,SerializeField.frame,HeaderSerialization.inputBase,writerBase,
      NativePrecision.final,rightCfg,ParsedPrecision.final,PrecisionProgram.final,
      PrecisionProgram.finalArithmetic,NativePrecision.caller,RequestHeaders.secondFinished,
      TapeExtension.embed,HeaderOffsets.finished,stopCfg,HeaderOffsets.rawFinished] <;> rfl
  · funext i
    fin_cases i <;> simp [handoff,HeaderSerialization.initial,leftCfg,
      HeaderSerialization.firstInitial,SerializeField.frame,HeaderSerialization.inputBase,writerBase,
      NativePrecision.final,rightCfg,ParsedPrecision.final,PrecisionProgram.final,
      PrecisionProgram.finalArithmetic,NativePrecision.caller,RequestHeaders.secondFinished,
      TapeExtension.embed,HeaderOffsets.finished,stopCfg,HeaderOffsets.rawFinished]

theorem final_output (x tail w v : List Bool) :
    (final x tail w v).cells 1 = machine.tapeOf
      ((HeaderSerialization.header (true::tail) ++ encNat (BinaryCounter.value v)).map machine.bitSym) := by
  simp [final,MachineSequence.rightCfg,HeaderSerialization.final,
    HeaderSerialization.precisionFinished,TapePermutation.embed,HeaderSerialization.swap34,
    Equiv.swap_apply_def,SerializeField.frame,HeaderSerialization.header,encNat,bin]
  rfl

end BitDFT.RewriteHeaders
open BitDFT BitDFT.RewriteHeaders IntMul

theorem solution (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (rest : List Bool) :
    let q := guardPrecision n b
    let x := encNat n ++ encNat b ++ rest
    ∃ t v, t ≤ 19*q ∧ BinaryCounter.value v = q ∧ v.length ≤ q ∧
      machine.step^[t] (machine.initCfg x []) =
        final x (bin n.size n).tail (bin b.size b) v := by
  dsimp only
  let q := guardPrecision n b
  let x := encNat n ++ encNat b ++ rest
  obtain ⟨tail,hnword,htail,hnval⟩ := RewriteCanonical.canonical n hn
  obtain ⟨s,v,hs,hv,hlen,hr⟩ := BitDFT.encoded_precision_correct n b hn hb rest
  rw [hnword,List.tail_cons] at hr
  have hq : 0 < q := by unfold q guardPrecision; omega
  have hval : 0 < BinaryCounter.value v := by rw [hv]; exact hq
  obtain ⟨u,hu,hw⟩ := BitDFT.header_serialization_correct
    (writerBase x tail (bin b.size b) v) (true::tail) v [] hval
  have hh : ((MachineSequence.native NativePrecision.machine).machine.step^[s]
      (NativePrecision.machine.initCfg x [])).state = (MachineSequence.native NativePrecision.machine).exit := by
    change (NativePrecision.machine.step^[s] (NativePrecision.machine.initCfg x [])).state = _
    rw [hr]; rfl
  obtain ⟨t,ht,he⟩ := BitDFT.machine_sequence_bound (MachineSequence.native NativePrecision.machine) writerControl
    (NativePrecision.machine.initCfg x []) s u hh
  change machine.step^[t] (machine.initCfg x []) =
    MachineSequence.rightCfg (MachineSequence.native NativePrecision.machine) writerControl
      (HeaderSerialization.machine.step^[u]
        (MachineSequence.handoff (MachineSequence.native NativePrecision.machine) writerControl
          (NativePrecision.machine.step^[s] (NativePrecision.machine.initCfg x [])))) at he
  rw [hr,writer_handoff,hw] at he
  refine ⟨t,v,?_,hv,hlen,?_⟩
  · have hnsize : n.size ≤ lg n+1 := by
      apply Nat.size_le.mpr
      have hnp : n ≤ 2^lg n := (Nat.le_pow_clog (by decide : 1<2) n).trans
        (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
      have hpos := Nat.two_pow_pos (lg n)
      rw [pow_succ]
      omega
    have hqs : q.size ≤ q := Nat.size_le.mpr Nat.lt_two_pow_self
    simp only [List.length_cons,hv] at hu
    change u ≤ 2*(tail.length+1)+2*v.length+2*q.size+12 at hu
    change s ≤ 11*q at hs
    change v.length ≤ q at hlen
    change t ≤ 19*q
    have hg : 1 ≤ lg n := le_max_right _ _
    have hqdef : q=b+3*lg n+5 := rfl
    omega
  · change machine.step^[t] (machine.initCfg x []) = final x tail (bin b.size b) v at he
    simpa only [hnword,List.tail_cons] using he

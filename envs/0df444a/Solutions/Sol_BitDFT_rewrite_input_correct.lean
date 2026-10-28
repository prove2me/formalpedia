-- Prove2me | solution 1 for BitDFT.rewrite_input_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:40:52.852238+00:00
-- url     : https://prove2.me/submissions/4c46dde5-8ebe-4d35-af70-b1bbae6ecf2d

import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn
import Definitions.Def_BitDFT_RewriteInput
import Theorems.Thm_BitDFT_rewrite_headers_correct
import Theorems.Thm_BitDFT_suffix_copy_correct
import Theorems.Thm_BitDFT_machine_sequence_bound

namespace BitDFT.InputCanonical
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

end BitDFT.InputCanonical


noncomputable section
namespace BitDFT.RewriteInput
open IntMul MachineSequence

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem copy_handoff (x tail w v : List Bool) :
    handoff (native RewriteHeaders.machine) copyControl (RewriteHeaders.final x tail w v) =
      SuffixCopy.frame (copyBase x tail w v) .copy x
        (HeaderSerialization.header (true::tail) ++ encNat (BinaryCounter.value v))
        ((HeaderSerialization.header (true::tail)).length+2*w.length+2) := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [handoff,copyBase,SuffixCopy.frame,
      RewriteHeaders.final,rightCfg,HeaderSerialization.final,HeaderSerialization.precisionFinished,
      TapePermutation.embed,HeaderSerialization.swap34,Equiv.swap_apply_def,SerializeField.frame,
      HeaderSerialization.serializerBase,HeaderSerialization.trimmed,TrimReverse.frame,
      HeaderSerialization.trimBase,HeaderSerialization.firstFinished,HeaderSerialization.inputBase,
      RewriteHeaders.writerBase,NativePrecision.final,ParsedPrecision.final,PrecisionProgram.final,
      PrecisionProgram.finalArithmetic,NativePrecision.caller,RequestHeaders.secondFinished,
      TapeExtension.embed,HeaderOffsets.finished,stopCfg,HeaderOffsets.rawFinished,
      HeaderSerialization.header,encNat,bin,List.append_assoc] <;> rfl
  · funext i
    fin_cases i <;> simp [handoff,copyBase,SuffixCopy.frame,
      RewriteHeaders.final,rightCfg,HeaderSerialization.final,HeaderSerialization.precisionFinished,
      TapePermutation.embed,HeaderSerialization.swap34,Equiv.swap_apply_def,SerializeField.frame,
      HeaderSerialization.serializerBase,HeaderSerialization.trimmed,TrimReverse.frame,
      HeaderSerialization.trimBase,HeaderSerialization.firstFinished,HeaderSerialization.inputBase,
      RewriteHeaders.writerBase,NativePrecision.final,ParsedPrecision.final,PrecisionProgram.final,
      PrecisionProgram.finalArithmetic,NativePrecision.caller,RequestHeaders.secondFinished,
      TapeExtension.embed,HeaderOffsets.finished,stopCfg,HeaderOffsets.rawFinished,
      HeaderSerialization.header,RequestHeaders.header,encNat,bin,List.append_assoc] <;> omega

end BitDFT.RewriteInput
open BitDFT BitDFT.RewriteInput IntMul

theorem solution (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (rest : List Bool) :
    let q := guardPrecision n b
    let x := encNat n ++ encNat b ++ rest
    ∃ t v, t ≤ 19*q+rest.length+2 ∧ BinaryCounter.value v = q ∧ v.length ≤ q ∧
      machine.step^[t] (machine.initCfg x []) = final n b rest v := by
  dsimp only
  let q := guardPrecision n b
  let x := encNat n ++ encNat b ++ rest
  obtain ⟨tail,hnword,htail,hnval⟩ := InputCanonical.canonical n hn
  obtain ⟨s,v,hs,hv,hlen,hr⟩ := BitDFT.rewrite_headers_correct n b hn hb rest
  rw [hnword,List.tail_cons] at hr
  have hh : ((MachineSequence.native RewriteHeaders.machine).machine.step^[s]
      (RewriteHeaders.machine.initCfg x [])).state = (MachineSequence.native RewriteHeaders.machine).exit := by
    change (RewriteHeaders.machine.step^[s] (RewriteHeaders.machine.initCfg x [])).state = _
    rw [hr]; rfl
  obtain ⟨t,ht,he⟩ := BitDFT.machine_sequence_bound (MachineSequence.native RewriteHeaders.machine) copyControl
    (RewriteHeaders.machine.initCfg x []) s (rest.length+1) hh
  change machine.step^[t] (machine.initCfg x []) =
    MachineSequence.rightCfg (MachineSequence.native RewriteHeaders.machine) copyControl
      (SuffixCopy.machine.step^[rest.length+1]
        (MachineSequence.handoff (MachineSequence.native RewriteHeaders.machine) copyControl
          (RewriteHeaders.machine.step^[s] (RewriteHeaders.machine.initCfg x [])))) at he
  rw [hr,copy_handoff,hv] at he
  have hheader : HeaderSerialization.header (true::tail) = encNat n := by
    rw [← hnword]; simp [HeaderSerialization.header,encNat,bin]
  rw [hheader] at he
  have hpos : (encNat n).length+2*(bin b.size b).length+2 = (encNat n++encNat b).length+1 := by
    simp [encNat,bin]; omega
  rw [hpos,BitDFT.suffix_copy_correct] at he
  refine ⟨t,v,by omega,hv,hlen,?_⟩
  unfold final
  rw [hnword,List.tail_cons]
  simpa only [x,List.length_append] using he

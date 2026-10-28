-- Prove2me | solution 1 for BitDFT.encoded_precision_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:16:44.577229+00:00
-- url     : https://prove2.me/submissions/49870642-bcb6-459a-b486-dfdf123fd3e5

import Theorems.Thm_BitDFT_native_precision_correct
import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn

namespace BitDFT.CanonicalHeaders
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

end BitDFT.CanonicalHeaders
open BitDFT IntMul BitDFT.NativePrecision

theorem solution (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (rest : List Bool) :
    let q := guardPrecision n b
    let x := encNat n ++ encNat b ++ rest
    ∃ t v, t ≤ 11*q ∧ BinaryCounter.value v = q ∧ v.length ≤ q ∧
      machine.step^[t] (machine.initCfg x []) =
        final x (bin n.size n).tail (bin b.size b) v := by
  dsimp only
  obtain ⟨tail,hnword,htail,hnval⟩ := CanonicalHeaders.canonical n hn
  have hbval : val (bin b.size b) = b := CanonicalHeaders.val_bin _ _ (Nat.lt_size_self b)
  have hbw : (bin b.size b).length ≤ val (bin b.size b) := by
    rw [hbval]
    simpa [bin] using (Nat.size_le.mpr (Nat.lt_two_pow_self) : b.size ≤ b)
  have hbpos : 1 ≤ val (bin b.size b) := by rwa [hbval]
  obtain ⟨t,v,ht,hv,hlen,hr⟩ := BitDFT.native_precision_correct tail (bin b.size b) rest hbpos hbw
  have hnheader : RequestHeaders.header (true::tail) = encNat n := by
    rw [← hnword]
    simp [RequestHeaders.header,encNat,bin]
  have hbheader : RequestHeaders.header (bin b.size b) = encNat b := by
    simp [RequestHeaders.header,encNat,bin]
  rw [hnval,hbval] at ht hv hlen
  rw [hnheader,hbheader] at hr
  refine ⟨t,v,?_,hv,hlen,?_⟩
  · have hnsize : n.size ≤ lg n+1 := by
      apply Nat.size_le.mpr
      have hnp : n ≤ 2^lg n := (Nat.le_pow_clog (by decide : 1<2) n).trans
        (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
      have hpos := Nat.two_pow_pos (lg n)
      rw [pow_succ]
      omega
    have hbs : b.size ≤ b := Nat.size_le.mpr Nat.lt_two_pow_self
    simp only [bin,List.length_ofFn] at ht
    unfold guardPrecision at ht ⊢
    omega
  · simpa only [hnword,List.tail_cons] using hr

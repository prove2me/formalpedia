-- Prove2me | solution 1 for BitcoinScript.castToBool_iff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T05:49:28.907995+00:00
-- url     : https://prove2.me/submissions/54bfecdf-97e5-4f21-a416-a04757fe6eb9

import Definitions.Def_BitcoinScript

open BitcoinScript

private theorem byte_lt (b : Byte) : b.toNat < 256 := b.isLt

private theorem and7f_toNat (b : Byte) : (b &&& 0x7f).toNat = b.toNat % 128 := by
  rw [BitVec.toNat_and]
  have h : (0x7f : Byte).toNat = 2 ^ 7 - 1 := rfl
  rw [h, Nat.and_two_pow_sub_one_eq_mod]

private theorem and_two_pow_eq (n k : Nat) : n &&& 2 ^ k = ((n / 2 ^ k) % 2) * 2 ^ k := by
  have h1 : (n &&& 2 ^ k) / 2 ^ k = (n / 2 ^ k) % 2 := by
    rw [Nat.and_div_two_pow, Nat.div_self (Nat.two_pow_pos k), Nat.and_one_is_mod]
  have h2 : (n &&& 2 ^ k) % 2 ^ k = 0 := by
    rw [Nat.and_mod_two_pow, Nat.mod_self, Nat.and_zero]
  have h := Nat.div_add_mod (n &&& 2 ^ k) (2 ^ k)
  rw [h1, h2, Nat.add_zero, Nat.mul_comm] at h
  exact h.symm

private theorem topbit_iff (b : Byte) : ((b &&& 0x80) != 0) = true ↔ 128 ≤ b.toNat := by
  have h := and_two_pow_eq b.toNat 7
  have h80 : (0x80 : Byte).toNat = 128 := rfl
  have h0 : (0 : Byte).toNat = 0 := rfl
  have hlt := byte_lt b
  rw [bne_iff_ne, ne_eq, BitVec.toNat_eq, BitVec.toNat_and, h80, h0]
  simp only [Nat.reducePow] at h
  rw [h]
  constructor <;> intro hh <;> omega

private theorem topbit_false_iff (b : Byte) : ((b &&& 0x80) != 0) = false ↔ b.toNat < 128 := by
  have := topbit_iff b
  cases h : ((b &&& 0x80) != 0)
  · rw [h] at this; simp at this; simp; omega
  · rw [h] at this; simp at this; simp; omega

private theorem or80_toNat (b : Byte) (hb : b.toNat < 128) : (b ||| 0x80).toNat = b.toNat + 128 := by
  rw [BitVec.toNat_or]
  have h80 : (0x80 : Byte).toNat = 128 := rfl
  rw [h80]
  have e : (128 : Nat) = 2 ^ 7 := rfl
  have hd : (b.toNat ||| 128) / 128 = 1 := by
    rw [e, Nat.or_div_two_pow, Nat.div_eq_of_lt (by simpa using hb), Nat.div_self (by decide)]
    rfl
  have hm : (b.toNat ||| 128) % 128 = b.toNat := by
    rw [e, Nat.or_mod_two_pow, Nat.mod_eq_of_lt (by simpa using hb), Nat.mod_self, Nat.or_zero]
  have := Nat.div_add_mod (b.toNat ||| 128) 128
  omega

private theorem leNat_append (l : Bytes) (b : Byte) :
    leNat (l ++ [b]) = leNat l + 256 ^ l.length * b.toNat := by
  induction l with
  | nil => simp [leNat]
  | cons x r ih =>
    simp only [List.cons_append, leNat, ih, List.length_cons, Nat.pow_succ]
    have : 256 ^ r.length * 256 * b.toNat = 256 * (256 ^ r.length * b.toNat) := by
      rw [Nat.mul_comm (256 ^ r.length) 256, Nat.mul_assoc]
    rw [this, Nat.mul_add]
    omega

private theorem topBit_append (l : Bytes) (b : Byte) : topBit (l ++ [b]) = ((b &&& 0x80) != 0) := by
  induction l with
  | nil => rfl
  | cons x r ih =>
    cases r with
    | nil => rfl
    | cons y r' => simp only [List.cons_append, topBit] at *; exact ih

private theorem clearTop_append (l : Bytes) (b : Byte) : clearTop (l ++ [b]) = l ++ [b &&& 0x7f] := by
  induction l with
  | nil => rfl
  | cons x r ih =>
    cases r with
    | nil => rfl
    | cons y r' => simp only [List.cons_append, clearTop] at *; rw [ih]

private theorem setTop_append (l : Bytes) (b : Byte) : setTop (l ++ [b]) = l ++ [b ||| 0x80] := by
  induction l with
  | nil => rfl
  | cons x r ih =>
    cases r with
    | nil => rfl
    | cons y r' => simp only [List.cons_append, setTop] at *; rw [ih]

private theorem concat_of_ne_nil (l : Bytes) (h : l ≠ []) : ∃ L b, l = L ++ [b] := by
  rcases List.eq_nil_or_concat l with h' | ⟨L, b, h'⟩
  · exact absurd h' h
  · exact ⟨L, b, by simpa using h'⟩

private theorem natBytes_zero : natBytes 0 = [] := by rw [natBytes]; rfl

private theorem natBytes_pos (n : Nat) (h : n ≠ 0) :
    natBytes n = BitVec.ofNat 8 (n % 256) :: natBytes (n / 256) := by
  rw [natBytes]; simp [h]

private theorem leNat_natBytes (n : Nat) : leNat (natBytes n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n = 0
    · subst h; rw [natBytes_zero]; rfl
    · rw [natBytes_pos n h]
      simp only [leNat]
      rw [ih (n / 256) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide))]
      rw [BitVec.toNat_ofNat]
      have : n % 256 % 2 ^ 8 = n % 256 :=
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
      rw [this]
      omega

private theorem natBytes_ne_nil (n : Nat) (h : n ≠ 0) : natBytes n ≠ [] := by
  rw [natBytes_pos n h]; simp

/-- The most significant byte produced by the serialization loop is nonzero. -/
private theorem natBytes_last_ne_zero (n : Nat) (L : Bytes) (b : Byte) (h : natBytes n = L ++ [b]) :
    b.toNat ≠ 0 := by
  induction n using Nat.strongRecOn generalizing L with
  | _ n ih =>
    by_cases h0 : n = 0
    · subst h0; rw [natBytes_zero] at h; simp at h
    · rw [natBytes_pos n h0] at h
      by_cases hq : n / 256 = 0
      · rw [hq, natBytes_zero] at h
        have : L = [] ∧ b = BitVec.ofNat 8 (n % 256) := by
          cases L with
          | nil => simp at h; exact ⟨rfl, h.symm⟩
          | cons x r => simp at h
        obtain ⟨-, rfl⟩ := this
        rw [BitVec.toNat_ofNat]
        have hn : n < 256 := by omega
        rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega)]
        exact h0
      · cases L with
        | nil =>
          simp at h
          have := congrArg List.length h.2
          simp at this
          exact absurd this (natBytes_ne_nil _ hq)
        | cons x r =>
          simp only [List.cons_append, List.cons.injEq] at h
          exact ih (n / 256) (Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)) r h.2

/-- The magnitude read by `set_vch`. -/
private def mag (v : Bytes) : Nat := if topBit v then leNat (clearTop v) else leNat v

private theorem setVch_eq (v : Bytes) : setVch v = if topBit v then -((mag v : Nat) : Int) else ((mag v : Nat) : Int) := by
  unfold setVch mag
  split <;> rfl

private theorem setVch_ne_zero_iff (v : Bytes) : setVch v ≠ 0 ↔ mag v ≠ 0 := by
  rw [setVch_eq]
  split <;> omega

private theorem mag_cons_cons (b c : Byte) (rest : Bytes) :
    mag (b :: c :: rest) = b.toNat + 256 * mag (c :: rest) := by
  unfold mag
  simp only [topBit, clearTop, leNat]
  split <;> rfl

private theorem mag_single (b : Byte) : mag [b] = if 128 ≤ b.toNat then b.toNat % 128 else b.toNat := by
  unfold mag
  simp only [topBit, clearTop, leNat, Nat.mul_zero, Nat.add_zero]
  by_cases h : 128 ≤ b.toNat
  · rw [if_pos ((topbit_iff b).2 h), if_pos h, and7f_toNat]
  · have : ((b &&& 0x80) != 0) = false := (topbit_false_iff b).2 (by omega)
    rw [this, if_neg h]; rfl

theorem solution (v : Bytes) : BitcoinScript.castToBool v = true ↔ BitcoinScript.setVch v ≠ 0 := by
  rw [setVch_ne_zero_iff]
  induction v with
  | nil => simp [castToBool, mag, topBit, leNat]
  | cons b rest ih =>
    cases rest with
    | nil =>
      simp only [castToBool, Bool.and_eq_true, bne_iff_ne, ne_eq, mag_single]
      have hlt := byte_lt b
      rw [BitVec.toNat_eq, BitVec.toNat_eq]
      have h0 : (0 : Byte).toNat = 0 := rfl
      have h80 : (0x80 : Byte).toNat = 128 := rfl
      rw [h0, h80]
      split <;> omega
    | cons c rest' =>
      simp only [castToBool, Bool.or_eq_true, bne_iff_ne, ne_eq, mag_cons_cons]
      rw [ih, BitVec.toNat_eq]
      have h0 : (0 : Byte).toNat = 0 := rfl
      rw [h0]
      omega

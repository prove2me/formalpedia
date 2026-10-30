-- Prove2me | solution 1 for BitcoinDifficulty.encoded_target_upper
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:06:36.718539+00:00
-- url     : https://prove2.me/submissions/fa1bd58f-78c0-434d-98c3-1369970352be

import Definitions.Def_BitcoinDifficulty
import Definitions.Def_BitcoinPow
open BitcoinDifficulty BitcoinPow

namespace S229BC

theorem L1 (N : Nat) (h : N < 2^24) : (N &&& 0x00800000 != 0) = decide (2^23 ≤ N) := by
  have key : N &&& 0x00800000 = if 2^23 ≤ N then 2^23 else 0 := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, show (0x00800000:Nat) = 2^23 from rfl, Nat.testBit_two_pow]
    by_cases hi : i = 23
    · subst hi
      by_cases hc : 2^23 ≤ N
      · rw [if_pos hc, Nat.testBit_two_pow_self, Nat.testBit_eq_decide_div_mod_eq]; simp; omega
      · rw [if_neg hc, Nat.zero_testBit, Nat.testBit_eq_decide_div_mod_eq]; simp; omega
    · have : decide (23 = i) = false := by simp; omega
      rw [this, Bool.and_false]
      split
      · rw [Nat.testBit_two_pow, this]
      · rw [Nat.zero_testBit]
  rw [key]
  by_cases hc : 2^23 ≤ N
  · rw [if_pos hc]; simp [hc]
  · rw [if_neg hc]; simp [hc]

theorem L23 (W s : Nat) (hW : W < 2^23) (hs : s < 256) :
    compactSize (BitVec.ofNat 32 (W ||| s <<< 24)) = s ∧ compactWord (BitVec.ofNat 32 (W ||| s <<< 24)) = W := by
  have e : W ||| s <<< 24 = s * 2^24 + W := by
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  rw [e]
  constructor
  · simp only [compactSize, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  · simp only [compactWord, BitVec.toNat_and, BitVec.toNat_ofNat]
    have : (8388607 : Nat) = 2^23 - 1 := by decide
    rw [show ((0x007fffff : BitVec 32)).toNat = 2^23 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega

theorem SC (W s : Nat) (hW : W < 2^23) (hs : s < 256) :
    setCompact (BitVec.ofNat 32 (W ||| s <<< 24)) =
      if s ≤ 3 then W / 2^(8*(3-s)) else W * 2^(8*(s-3)) % width := by
  obtain ⟨h1, h2⟩ := L23 W s hW hs
  unfold setCompact
  simp only [h1, h2]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]


theorem bitLength_spec (v : Nat) : v < 2^(bitLength v) ∧ (v ≠ 0 → 2^(bitLength v - 1) ≤ v) := by
  unfold bitLength
  by_cases h : v = 0
  · subst h; simp
  · simp only [h, if_false]
    exact ⟨Nat.lt_log2_self, fun _ => by simpa using Nat.log2_self_le h⟩

theorem round_spec (v : Nat) (hv : v < 2^248) : ∃ e, 8 ∣ e ∧
    setCompact (getCompact v) = v / 2^e * 2^e ∧ v < 2^(e+23) ∧ (e = 0 ∨ 2^(e+15) ≤ v) := by
  obtain ⟨hL, hL2⟩ := bitLength_spec v
  have hLle : bitLength v ≤ 248 := by
    unfold bitLength; split
    · omega
    · have := (Nat.log2_lt (n := v) (k := 248) (by omega)).2 hv; omega
  generalize hn : (bitLength v + 7) / 8 = n
  have hg : ∀ N, (if n ≤ 3 then (v % 2^64) <<< (8*(3-n)) % 2^32 else v >>> (8*(n-3)) % 2^64 % 2^32) = N →
      getCompact v = BitVec.ofNat 32 ((if (N &&& 0x00800000 != 0) = true then N >>> 8 else N) |||
        (if (N &&& 0x00800000 != 0) = true then n + 1 else n) <<< 24) := by
    intro N hN; subst hN; subst hn; rfl
  have hvn : v < 2^(8*n) := Nat.lt_of_lt_of_le hL (Nat.pow_le_pow_right (by omega) (by omega))
  have hvn2 : 1 ≤ n → 2^(8*(n-1)) ≤ v := by
    intro h1
    have hv0 : v ≠ 0 := by intro h0; subst h0; simp [bitLength] at hn; omega
    exact Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) (hL2 hv0)
  by_cases h3 : n ≤ 3
  · have hlt : v * 2^(8*(3-n)) < 2^24 := by
      calc v * 2^(8*(3-n)) < 2^(8*n) * 2^(8*(3-n)) := Nat.mul_lt_mul_of_pos_right hvn (Nat.two_pow_pos _)
        _ = 2^24 := by rw [← Nat.pow_add]; congr 1; omega
    have hN : (if n ≤ 3 then (v % 2^64) <<< (8*(3-n)) % 2^32 else v >>> (8*(n-3)) % 2^64 % 2^32) = v * 2^(8*(3-n)) := by
      have : v ≤ v * 2^(8*(3-n)) := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
      rw [if_pos h3, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (a := v) (b := 2^64) (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hg _ hN, L1 _ hlt]
    have hvN : v ≤ v * 2^(8*(3-n)) := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    by_cases hA : 2^23 ≤ v * 2^(8*(3-n))
    · simp only [decide_eq_true hA, if_true]
      rw [Nat.shiftRight_eq_div_pow, SC _ _ (by omega) (by omega)]
      rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) with rfl|rfl|rfl|rfl
      · simp only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceAdd] at hvn hA; omega
      · refine ⟨0, ⟨0, rfl⟩, ?_, ?_, Or.inl rfl⟩
        · simp only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceAdd, Nat.reduceLeDiff, if_true]; omega
        · simp only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceAdd] at hvn ⊢; omega
      · refine ⟨0, ⟨0, rfl⟩, ?_, ?_, Or.inl rfl⟩
        · simp only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceAdd, Nat.reduceLeDiff, if_true]; omega
        · simp only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceAdd] at hvn ⊢; omega
      · refine ⟨8, ⟨1, rfl⟩, ?_, ?_, Or.inr ?_⟩
        · simp only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceAdd, Nat.reduceLeDiff, if_false, width]
          simp only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceAdd] at hvn
          omega
        · simp only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceAdd] at hvn ⊢; omega
        · simp only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceAdd] at hA ⊢; omega
    · simp only [decide_eq_false hA, if_false, Bool.false_eq_true]
      rw [SC _ _ (by omega) (by omega)]
      refine ⟨0, ⟨0, rfl⟩, ?_, ?_, Or.inl rfl⟩
      · rw [if_pos h3, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]; simp
      · simp only [Nat.zero_add]; omega
  · have hk : 8*n = 8*(n-3) + 24 := by omega
    have hlt : v / 2^(8*(n-3)) < 2^24 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
      rw [hk] at hvn; rwa [Nat.add_comm] at hvn
    have hN : (if n ≤ 3 then (v % 2^64) <<< (8*(3-n)) % 2^32 else v >>> (8*(n-3)) % 2^64 % 2^32) = v / 2^(8*(n-3)) := by
      rw [if_neg h3, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (a := v / 2^(8*(n-3))) (b := 2^64) (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hg _ hN, L1 _ hlt]
    have hwid : v < width := Nat.lt_of_lt_of_le hv (by unfold width; exact Nat.pow_le_pow_right (by omega) (by omega))
    have hpk := Nat.two_pow_pos (8*(n-3))
    by_cases hA : 2^23 ≤ v / 2^(8*(n-3))
    · simp only [decide_eq_true hA, if_true]
      rw [Nat.shiftRight_eq_div_pow, SC _ _ (by omega) (by omega), if_neg (by omega),
        Nat.div_div_eq_div_mul, ← Nat.pow_add]
      have he : 8 * (n + 1 - 3) = 8*(n-3) + 8 := by omega
      rw [he]
      refine ⟨8*(n-3) + 8, ⟨n-2, by omega⟩, ?_, ?_, Or.inr ?_⟩
      · exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hwid)
      · rw [hk] at hvn; exact Nat.lt_of_lt_of_le hvn (Nat.pow_le_pow_right (by omega) (by omega))
      · have := (Nat.le_div_iff_mul_le hpk).1 hA
        rw [Nat.add_assoc, show 8 + 15 = 23 from rfl, Nat.pow_add, Nat.mul_comm]; exact this
    · simp only [decide_eq_false hA, if_false, Bool.false_eq_true]
      rw [SC _ _ (by omega) (by omega), if_neg h3]
      refine ⟨8*(n-3), ⟨n-3, rfl⟩, ?_, ?_, Or.inr ?_⟩
      · exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hwid)
      · have : v / 2^(8*(n-3)) < 2^23 := by omega
        rw [Nat.div_lt_iff_lt_mul hpk, ← Nat.pow_add, Nat.add_comm] at this; exact this
      · have := hvn2 (by omega)
        exact Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) this

theorem raw_bounds (t : Nat) (ht : t ≤ BitcoinPow.powLimit) (lastTime firstTime : Int) :
    BitcoinDifficulty.rawNextTarget t lastTime firstTime ≤ 4 * t ∧
    (BitcoinDifficulty.rawNextTarget t lastTime firstTime = BitcoinPow.powLimit ∨
      t / 4 ≤ BitcoinDifficulty.rawNextTarget t lastTime firstTime) := by
  have hc : (302400 : Int) ≤ clampTimespan (lastTime - firstTime) ∧
      clampTimespan (lastTime - firstTime) ≤ 4838400 := by
    have e1 : ((14 * 24 * 60 * 60 / 4 : Nat) : Int) = 302400 := by decide
    have e2 : ((14 * 24 * 60 * 60 * 4 : Nat) : Int) = 4838400 := by decide
    simp only [clampTimespan, targetTimespan, e1, e2]
    by_cases ha : lastTime - firstTime < 302400
    · simp only [ha, if_true]; omega
    · by_cases hb : 4838400 < lastTime - firstTime
      · simp only [ha, hb, if_true, if_false]; omega
      · simp only [ha, hb, if_false]; omega
  have h1 : 302400 ≤ (clampTimespan (lastTime - firstTime)).toNat := by omega
  have h2 : (clampTimespan (lastTime - firstTime)).toNat ≤ 4838400 := by omega
  generalize hcd : (clampTimespan (lastTime - firstTime)).toNat = c at h1 h2
  have hw : t * c < width := by
    calc t * c ≤ powLimit * 4838400 := Nat.mul_le_mul ht h2
      _ < width := by unfold powLimit width; decide
  have hb : (t * c) % width / targetTimespan = t * c / 1209600 := by
    rw [Nat.mod_eq_of_lt hw]; rfl
  have hup : t * c / 1209600 ≤ 4 * t := by
    apply Nat.div_le_of_le_mul
    have := Nat.mul_le_mul_left t h2
    clear hw hb hc hcd ht
    omega
  have hlo : t / 4 ≤ t * c / 1209600 := by
    apply (Nat.le_div_iff_mul_le (by decide)).2
    have h3 := Nat.mul_le_mul_left t h1
    have h4 : t / 4 * 4 * 302400 ≤ t * 302400 := Nat.mul_le_mul_right _ (Nat.div_mul_le_self t 4)
    calc t / 4 * 1209600 = t / 4 * 4 * 302400 := by rw [Nat.mul_assoc]
      _ ≤ t * c := Nat.le_trans h4 h3
  have hr : rawNextTarget t lastTime firstTime =
      (if powLimit < (t * c) % width / targetTimespan then powLimit else (t * c) % width / targetTimespan) := by
    rw [← hcd]; rfl
  rw [hr, hb]
  by_cases hp : powLimit < t * c / 1209600
  · rw [if_pos hp]; exact ⟨by omega, Or.inl rfl⟩
  · rw [if_neg hp]; exact ⟨hup, Or.inr hlo⟩

theorem round_le (v : Nat) (hv : v < 2^248) : setCompact (getCompact v) ≤ v := by
  obtain ⟨e, _, h, _⟩ := round_spec v hv
  rw [h]; exact Nat.div_mul_le_self _ _

theorem round_mono (v w : Nat) (hw : w < 2^248) (hvw : v ≤ w) :
    setCompact (getCompact v) ≤ setCompact (getCompact w) := by
  obtain ⟨a, ha8, hva, hva1, _⟩ := round_spec v (Nat.lt_of_le_of_lt hvw hw)
  obtain ⟨b, hb8, hwb, _, hwb2⟩ := round_spec w hw
  rw [hva, hwb]
  by_cases hab : b ≤ a
  · have hpb := Nat.two_pow_pos b
    have h1 : v / 2^a * 2^(a-b) ≤ v / 2^b := by
      apply (Nat.le_div_iff_mul_le hpb).2
      rw [Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel hab]
      exact Nat.div_mul_le_self _ _
    calc v / 2^a * 2^a = v / 2^a * 2^(a-b) * 2^b := by
            rw [Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel hab]
      _ ≤ v / 2^b * 2^b := Nat.mul_le_mul_right _ h1
      _ ≤ w / 2^b * 2^b := Nat.mul_le_mul_right _ (Nat.div_le_div_right hvw)
  · have hab8 : a + 8 ≤ b := by omega
    have hw15 : 2^(b+15) ≤ w := by
      rcases hwb2 with h | h
      · omega
      · exact h
    have h2 : 2^15 ≤ w / 2^b := by
      apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos b)).2
      rw [← Nat.pow_add, Nat.add_comm]; exact hw15
    apply Nat.le_of_lt
    calc v / 2^a * 2^a ≤ v := Nat.div_mul_le_self _ _
      _ < 2^(a+23) := hva1
      _ ≤ 2^(b+15) := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 2^15 * 2^b := by rw [Nat.add_comm, Nat.pow_add]
      _ ≤ w / 2^b * 2^b := Nat.mul_le_mul_right _ h2

theorem powLimit_lt : powLimit < 2^248 := by unfold powLimit; decide

theorem raw_le_powLimit (t : Nat) (l f : Int) : BitcoinDifficulty.rawNextTarget t l f ≤ powLimit := by
  unfold BitcoinDifficulty.rawNextTarget
  simp only []
  split
  · exact Nat.le_refl _
  · omega

theorem calc_eq (bits : BitVec 32) (l f : Int) :
    calculateNextWork bits l f = getCompact (BitcoinDifficulty.rawNextTarget (setCompact bits) l f) := rfl

theorem step_le (bits : BitVec 32) (l f : Int) :
    setCompact (calculateNextWork bits l f) ≤ BitcoinDifficulty.rawNextTarget (setCompact bits) l f := by
  rw [calc_eq]
  exact round_le _ (Nat.lt_of_le_of_lt (raw_le_powLimit _ _ _) powLimit_lt)

theorem step_upper (bits : BitVec 32) (hb : setCompact bits ≤ powLimit) (l f : Int) :
    setCompact (calculateNextWork bits l f) ≤ 4 * setCompact bits :=
  Nat.le_trans (step_le bits l f) (raw_bounds _ hb l f).1

theorem step_powLimit (bits : BitVec 32) (l f : Int) :
    setCompact (calculateNextWork bits l f) ≤ powLimit :=
  Nat.le_trans (step_le bits l f) (raw_le_powLimit _ _ _)

end S229BC

open S229BC in
theorem solution (bits : BitVec 32) (hb : BitcoinPow.setCompact bits ≤ BitcoinPow.powLimit)
    (lastTime firstTime : Int) :
    BitcoinPow.setCompact (BitcoinPow.calculateNextWork bits lastTime firstTime) ≤ 4 * BitcoinPow.setCompact bits :=
  step_upper bits hb lastTime firstTime

-- Prove2me | solution 1 for BitcoinPow.getCompact_valid
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:55.17621+00:00
-- url     : https://prove2.me/submissions/cd2e3ecf-8b9b-4379-a064-7330d7bf0898

import Definitions.Def_BitcoinPow

open BitcoinPow

/-- Conjunction with a single power of two isolates that bit. -/
private theorem and_two_pow_eq (n k : Nat) : n &&& 2 ^ k = ((n / 2 ^ k) % 2) * 2 ^ k := by
  have h1 : (n &&& 2 ^ k) / 2 ^ k = (n / 2 ^ k) % 2 := by
    rw [Nat.and_div_two_pow, Nat.div_self (Nat.two_pow_pos k), Nat.and_one_is_mod]
  have h2 : (n &&& 2 ^ k) % 2 ^ k = 0 := by
    rw [Nat.and_mod_two_pow, Nat.mod_self, Nat.and_zero]
  have h := Nat.div_add_mod (n &&& 2 ^ k) (2 ^ k)
  rw [h1, h2, Nat.add_zero, Nat.mul_comm] at h
  exact h.symm

/-- Fields of a compact word assembled as `mantissa ||| size <<< 24` with a 23-bit mantissa. -/
private theorem fields_of_assembled (a n : Nat) (ha : a < 2 ^ 23) (hn : n < 256) :
    compactSize (BitVec.ofNat 32 (a ||| n <<< 24)) = n ∧
    compactWord (BitVec.ofNat 32 (a ||| n <<< 24)) = a ∧
    compactNegative (BitVec.ofNat 32 (a ||| n <<< 24)) = false := by
  have hx : a ||| n <<< 24 < 2 ^ 32 := by
    apply Nat.or_lt_two_pow
    · exact Nat.lt_trans ha (by decide)
    · rw [Nat.shiftLeft_eq]
      calc n * 2 ^ 24 < 256 * 2 ^ 24 := Nat.mul_lt_mul_of_pos_right hn (by decide)
        _ = 2 ^ 32 := by decide
  have htoNat : (BitVec.ofNat 32 (a ||| n <<< 24)).toNat = a ||| n <<< 24 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hx
  have hdiv24 : (a ||| n <<< 24) / 2 ^ 24 = n := by
    rw [Nat.or_div_two_pow, Nat.div_eq_of_lt (Nat.lt_trans ha (by decide)), Nat.zero_or,
      ← Nat.shiftRight_eq_div_pow, Nat.shiftLeft_shiftRight]
  have hmod23 : (a ||| n <<< 24) % 2 ^ 23 = a := by
    rw [Nat.or_mod_two_pow, Nat.mod_eq_of_lt ha, Nat.shiftLeft_eq]
    have : n * 2 ^ 24 = (n * 2) * 2 ^ 23 := by rw [Nat.mul_assoc]
    rw [this, Nat.mul_mod_left, Nat.or_zero]
  have hdiv23 : (a ||| n <<< 24) / 2 ^ 23 = n * 2 := by
    rw [Nat.or_div_two_pow, Nat.div_eq_of_lt ha, Nat.zero_or, Nat.shiftLeft_eq]
    have : n * 2 ^ 24 = (n * 2) * 2 ^ 23 := by rw [Nat.mul_assoc]
    rw [this, Nat.mul_div_cancel _ (Nat.two_pow_pos 23)]
  refine ⟨?_, ?_, ?_⟩
  · unfold compactSize
    rw [BitVec.toNat_ushiftRight, htoNat, Nat.shiftRight_eq_div_pow, hdiv24]
  · unfold compactWord
    rw [BitVec.toNat_and, htoNat]
    have h : (0x007fffff : BitVec 32).toNat = 2 ^ 23 - 1 := rfl
    rw [h, Nat.and_two_pow_sub_one_eq_mod, hmod23]
  · unfold compactNegative
    have hbit : ((BitVec.ofNat 32 (a ||| n <<< 24)) &&& 0x00800000) = 0 := by
      rw [BitVec.toNat_eq, BitVec.toNat_and, htoNat]
      have h : (0x00800000 : BitVec 32).toNat = 2 ^ 23 := rfl
      have h0 : (0 : BitVec 32).toNat = 0 := rfl
      rw [h, h0, and_two_pow_eq, hdiv23]
      simp [Nat.mul_mod_left]
    rw [hbit]
    simp

/-- The mantissa bit test is a comparison against `2 ^ 23` for 24-bit values. -/
private theorem adjust_iff (m : Nat) (hm : m < 2 ^ 24) :
    (m &&& 0x00800000 != 0) = true ↔ 2 ^ 23 ≤ m := by
  have h : (0x00800000 : Nat) = 2 ^ 23 := by decide
  rw [bne_iff_ne, ne_eq, h, and_two_pow_eq]
  constructor
  · intro hne
    rcases Nat.lt_or_ge m (2 ^ 23) with hlt | hge
    · exfalso; apply hne; rw [Nat.div_eq_of_lt hlt]
    · exact hge
  · intro hge
    have h1 : m / 2 ^ 23 = 1 := by
      have := Nat.div_le_div_right (c := 2 ^ 23) (Nat.le_of_lt hm)
      have h2 : 2 ^ 24 / 2 ^ 23 = 2 := by decide
      have h3 : 1 ≤ m / 2 ^ 23 := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2 (by simpa using hge)
      omega
    rw [h1]; decide

private theorem bitLength_eq (v : Nat) (hv : v ≠ 0) : bitLength v = Nat.log2 v + 1 := by
  unfold bitLength; rw [if_neg hv]

/-- Any word assembled by GetCompact's final step from a 24-bit mantissa and a size at most 32
decodes as non-negative and non-overflowing. -/
private theorem assembled_valid (M n0 : Nat) (hM : M < 2 ^ 24) (hn : n0 ≤ 32) :
    compactNegative (BitVec.ofNat 32
      ((if (M &&& 0x00800000 != 0) = true then M >>> 8 else M) |||
        (if (M &&& 0x00800000 != 0) = true then n0 + 1 else n0) <<< 24)) = false ∧
    compactOverflow (BitVec.ofNat 32
      ((if (M &&& 0x00800000 != 0) = true then M >>> 8 else M) |||
        (if (M &&& 0x00800000 != 0) = true then n0 + 1 else n0) <<< 24)) = false := by
  by_cases hadj : (M &&& 0x00800000 != 0) = true
  · simp only [if_pos hadj]
    have hm : M >>> 8 < 2 ^ 16 := by
      rw [Nat.shiftRight_eq_div_pow]
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
      exact Nat.lt_of_lt_of_le hM (by decide)
    have hm23 : M >>> 8 < 2 ^ 23 := Nat.lt_of_lt_of_le hm (by decide)
    obtain ⟨hs, hw, hneg⟩ := fields_of_assembled (M >>> 8) (n0 + 1) hm23 (by omega)
    refine ⟨hneg, ?_⟩
    unfold compactOverflow
    rw [hs, hw]
    generalize hm' : M >>> 8 = m at *
    simp only [bne_iff_ne, ne_eq, Bool.and_eq_false_imp, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      Nat.not_lt]
    intro _
    refine ⟨⟨by omega, fun _ => by omega⟩, fun h => ?_⟩
    simp only [decide_eq_true_eq] at h
    omega
  · simp only [if_neg hadj]
    have hm23 : M < 2 ^ 23 := by
      rcases Nat.lt_or_ge M (2 ^ 23) with hlt | hge
      · exact hlt
      · exact absurd ((adjust_iff M hM).2 hge) hadj
    obtain ⟨hs, hw, hneg⟩ := fields_of_assembled M n0 hm23 (by omega)
    refine ⟨hneg, ?_⟩
    unfold compactOverflow
    rw [hs, hw]
    simp only [bne_iff_ne, ne_eq, Bool.and_eq_false_imp, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      Nat.not_lt]
    intro _
    exact ⟨⟨by omega, fun _ => by omega⟩, fun _ => by omega⟩

theorem solution (v : Nat) (hv : v < BitcoinPow.width) :
    BitcoinPow.compactNegative (BitcoinPow.getCompact v) = false ∧
    BitcoinPow.compactOverflow (BitcoinPow.getCompact v) = false := by
  by_cases hv0 : v = 0
  · subst hv0; decide
  have hL := Nat.log2_self_le hv0
  have hL' := @Nat.lt_log2_self v
  have hL256 : Nat.log2 v < 256 := (Nat.log2_lt hv0).2 hv
  unfold getCompact
  rw [bitLength_eq v hv0]
  generalize hLdef : Nat.log2 v = L at *
  have hsize : (L + 1 + 7) / 8 = L / 8 + 1 := by omega
  rw [hsize]
  simp only []
  apply assembled_valid
  · -- the pre-adjustment mantissa is below 2^24
    split
    · rename_i h3
      have hv64 : v % 2 ^ 64 = v :=
        Nat.mod_eq_of_lt (Nat.lt_trans hL' (Nat.pow_lt_pow_right (by decide) (by omega)))
      rw [hv64, Nat.shiftLeft_eq]
      have hbound : v * 2 ^ (8 * (3 - (L / 8 + 1))) < 2 ^ 24 := by
        calc v * 2 ^ (8 * (3 - (L / 8 + 1))) < 2 ^ (L + 1) * 2 ^ (8 * (3 - (L / 8 + 1))) :=
              Nat.mul_lt_mul_of_pos_right hL' (Nat.two_pow_pos _)
          _ = 2 ^ ((L + 1) + 8 * (3 - (L / 8 + 1))) := (Nat.pow_add _ _ _).symm
          _ ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hbound
    · rename_i h3
      rw [Nat.shiftRight_eq_div_pow]
      have hbound : v / 2 ^ (8 * (L / 8 + 1 - 3)) < 2 ^ 24 := by
        apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
        rw [← Nat.pow_add]
        exact Nat.lt_of_lt_of_le hL' (Nat.pow_le_pow_right (by decide) (by omega))
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hbound)
  · omega

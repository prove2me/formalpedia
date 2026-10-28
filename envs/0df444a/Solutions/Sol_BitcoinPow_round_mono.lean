-- Prove2me | solution 1 for BitcoinPow.round_mono
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:55.764274+00:00
-- url     : https://prove2.me/submissions/a69e066c-c599-4d73-9b8f-fff2dfe3f4e1

import Definitions.Def_BitcoinPow
import Theorems.Thm_BitcoinPow_getCompact_le

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

/-- Number of low bits that `GetCompact` discards, as a function of the index of the top bit. -/
private def dropBits (L : Nat) : Nat :=
  if L < 16 then 0 else 8 * (L / 8) - 16 + (if L % 8 = 7 then 8 else 0)

private theorem dropBits_le (L : Nat) : dropBits L ≤ L := by
  unfold dropBits
  split
  · exact Nat.zero_le _
  · split <;> omega

/-- The core identity: `SetCompact ∘ GetCompact` clears the low `dropBits (log2 v)` bits of `v`. -/
private theorem round_eq (v : Nat) (hv0 : v ≠ 0) (hv : v < 2 ^ 256) :
    setCompact (getCompact v) =
      (v / 2 ^ dropBits (Nat.log2 v)) * 2 ^ dropBits (Nat.log2 v) := by
  have hL := Nat.log2_self_le hv0
  have hL' := @Nat.lt_log2_self v
  have hL256 : Nat.log2 v < 256 := (Nat.log2_lt hv0).2 hv
  generalize hLdef : Nat.log2 v = L at *
  have hmod8 : L % 8 < 8 := Nat.mod_lt _ (by decide)
  unfold getCompact
  rw [bitLength_eq v hv0, hLdef]
  have hsize : (L + 1 + 7) / 8 = L / 8 + 1 := by omega
  rw [hsize]
  simp only []
  rcases Nat.lt_or_ge L 24 with hsmall | hbig
  · -- nSize ≤ 3: mantissa = v * 2 ^ k, k = 8 * (2 - L / 8)
    have h3 : L / 8 + 1 ≤ 3 := by omega
    rw [if_pos h3]
    have hv64 : v % 2 ^ 64 = v :=
      Nat.mod_eq_of_lt (Nat.lt_trans hL' (Nat.pow_lt_pow_right (by decide) (by omega)))
    rw [hv64, Nat.shiftLeft_eq]
    have hk : 8 * (3 - (L / 8 + 1)) = 8 * (2 - L / 8) := by omega
    rw [hk]
    generalize hkdef : 8 * (2 - L / 8) = k
    have hmant_lo : 2 ^ (L % 8 + 16) ≤ v * 2 ^ k := by
      have : L % 8 + 16 = L + k := by omega
      rw [this, Nat.pow_add]; exact Nat.mul_le_mul_right _ hL
    have hmant_hi : v * 2 ^ k < 2 ^ (L % 8 + 17) := by
      have : L % 8 + 17 = (L + 1) + k := by omega
      rw [this, Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right hL' (Nat.two_pow_pos _)
    have hmant24 : v * 2 ^ k < 2 ^ 24 :=
      Nat.lt_of_lt_of_le hmant_hi (Nat.pow_le_pow_right (by decide) (by omega))
    have hmant32 : v * 2 ^ k % 2 ^ 32 = v * 2 ^ k :=
      Nat.mod_eq_of_lt (Nat.lt_trans hmant24 (by decide))
    rw [hmant32]
    by_cases hadj : (v * 2 ^ k &&& 0x00800000 != 0) = true
    · -- adjust: L % 8 = 7, so L ∈ {7, 15, 23}
      have h23 : 2 ^ 23 ≤ v * 2 ^ k := (adjust_iff _ hmant24).1 hadj
      have hL7 : L % 8 = 7 := by
        rcases Nat.lt_or_ge (L % 8) 7 with hlt | hge
        · exfalso
          have hlt23 : L % 8 + 17 ≤ 23 := by omega
          have : v * 2 ^ k < 2 ^ 23 :=
            Nat.lt_of_lt_of_le hmant_hi (Nat.pow_le_pow_right (by decide) hlt23)
          omega
        · omega
      simp only [if_pos hadj]
      by_cases h16 : L < 16
      · -- L ∈ {7, 15}: the adjusted word still has nSize' ≤ 3, result exact
        have hk8 : 8 ≤ k := by omega
        have hm' : (v * 2 ^ k) >>> 8 = v * 2 ^ (k - 8) := by
          rw [Nat.shiftRight_eq_div_pow]
          have : 2 ^ k = 2 ^ (k - 8) * 2 ^ 8 := by rw [← Nat.pow_add]; congr 1; omega
          rw [this, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos 8)]
        rw [hm']
        have ha : v * 2 ^ (k - 8) < 2 ^ 23 := by
          have hsplit : v * 2 ^ k = v * 2 ^ (k - 8) * 2 ^ 8 := by
            rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
          rw [hsplit] at hmant24
          have h24 : (2 : Nat) ^ 24 = 2 ^ 16 * 2 ^ 8 := by rw [← Nat.pow_add]
          rw [h24] at hmant24
          exact Nat.lt_of_lt_of_le (Nat.lt_of_mul_lt_mul_right hmant24)
            (Nat.pow_le_pow_right (by decide) (by decide))
        obtain ⟨hs, hw, -⟩ := fields_of_assembled (v * 2 ^ (k - 8)) (L / 8 + 1 + 1) ha (by omega)
        simp only [setCompact, hs, hw]
        have h3' : L / 8 + 1 + 1 ≤ 3 := by omega
        rw [if_pos h3', Nat.shiftRight_eq_div_pow]
        have hdrop : dropBits L = 0 := by unfold dropBits; rw [if_pos h16]
        rw [hdrop]
        simp only [Nat.pow_zero, Nat.div_one, Nat.mul_one]
        have : 8 * (3 - (L / 8 + 1 + 1)) = k - 8 := by omega
        rw [this, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
      · -- L = 23: k = 0, the adjusted word has nSize' = 4
        have hk0 : k = 0 := by omega
        have hm' : (v * 2 ^ k) >>> 8 = v / 2 ^ 8 := by
          rw [hk0, Nat.pow_zero, Nat.mul_one, Nat.shiftRight_eq_div_pow]
        rw [hm']
        have ha : v / 2 ^ 8 < 2 ^ 23 := by
          apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
          rw [hk0, Nat.pow_zero, Nat.mul_one] at hmant24
          exact Nat.lt_of_lt_of_le hmant24 (by decide)
        obtain ⟨hs, hw, -⟩ := fields_of_assembled (v / 2 ^ 8) (L / 8 + 1 + 1) ha (by omega)
        simp only [setCompact, hs, hw]
        have h3' : ¬ (L / 8 + 1 + 1 ≤ 3) := by omega
        rw [if_neg h3', Nat.shiftLeft_eq]
        have hexp : 8 * (L / 8 + 1 + 1 - 3) = 8 := by omega
        rw [hexp]
        have hdrop : dropBits L = 8 := by
          unfold dropBits; rw [if_neg h16, if_pos hL7]; omega
        rw [hdrop]
        apply Nat.mod_eq_of_lt
        exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hv
    · -- no adjust: result exact
      simp only [if_neg hadj]
      have ha : v * 2 ^ k < 2 ^ 23 := by
        rcases Nat.lt_or_ge (v * 2 ^ k) (2 ^ 23) with hlt | hge
        · exact hlt
        · exact absurd ((adjust_iff _ hmant24).2 hge) hadj
      obtain ⟨hs, hw, -⟩ := fields_of_assembled (v * 2 ^ k) (L / 8 + 1) ha (by omega)
      simp only [setCompact, hs, hw]
      rw [if_pos h3, Nat.shiftRight_eq_div_pow]
      have hL7 : L % 8 ≠ 7 := by
        intro h7
        apply hadj
        apply (adjust_iff _ hmant24).2
        calc 2 ^ 23 = 2 ^ (L % 8 + 16) := by rw [h7]
          _ ≤ v * 2 ^ k := hmant_lo
      have hdrop : dropBits L = 0 := by
        unfold dropBits
        by_cases h16 : L < 16
        · rw [if_pos h16]
        · rw [if_neg h16, if_neg hL7]; omega
      rw [hdrop]
      simp only [Nat.pow_zero, Nat.div_one, Nat.mul_one]
      have : 8 * (3 - (L / 8 + 1)) = k := by omega
      rw [this, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  · -- nSize > 3: mantissa = v / 2 ^ s with s = 8 * (L / 8) - 16
    have h3 : ¬ (L / 8 + 1 ≤ 3) := by omega
    rw [if_neg h3, Nat.shiftRight_eq_div_pow]
    have hs : 8 * (L / 8 + 1 - 3) = 8 * (L / 8) - 16 := by omega
    rw [hs]
    generalize hsdef : 8 * (L / 8) - 16 = s
    have hmant_lo : 2 ^ (L % 8 + 16) ≤ v / 2 ^ s := by
      apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2
      rw [← Nat.pow_add]
      have : L % 8 + 16 + s = L := by omega
      rw [this]; exact hL
    have hmant_hi : v / 2 ^ s < 2 ^ (L % 8 + 17) := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
      rw [← Nat.pow_add]
      have : L % 8 + 17 + s = L + 1 := by omega
      rw [this]; exact hL'
    have hmant24 : v / 2 ^ s < 2 ^ 24 :=
      Nat.lt_of_lt_of_le hmant_hi (Nat.pow_le_pow_right (by decide) (by omega))
    have hmant64 : v / 2 ^ s % 2 ^ 64 = v / 2 ^ s :=
      Nat.mod_eq_of_lt (Nat.lt_trans hmant24 (by decide))
    have hmant32 : v / 2 ^ s % 2 ^ 32 = v / 2 ^ s :=
      Nat.mod_eq_of_lt (Nat.lt_trans hmant24 (by decide))
    rw [hmant64, hmant32]
    have hdrop_lt : ¬ (L < 16) := by omega
    by_cases hadj : (v / 2 ^ s &&& 0x00800000 != 0) = true
    · have h23 : 2 ^ 23 ≤ v / 2 ^ s := (adjust_iff _ hmant24).1 hadj
      have hL7 : L % 8 = 7 := by
        rcases Nat.lt_or_ge (L % 8) 7 with hlt | hge
        · exfalso
          have hlt23 : L % 8 + 17 ≤ 23 := by omega
          have : v / 2 ^ s < 2 ^ 23 :=
            Nat.lt_of_lt_of_le hmant_hi (Nat.pow_le_pow_right (by decide) hlt23)
          omega
        · omega
      simp only [if_pos hadj]
      have hm' : (v / 2 ^ s) >>> 8 = v / 2 ^ (s + 8) := by
        rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]
      rw [hm']
      have ha : v / 2 ^ (s + 8) < 2 ^ 23 := by
        rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]
        apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
        exact Nat.lt_of_lt_of_le hmant24 (by decide)
      obtain ⟨hsz, hw, -⟩ := fields_of_assembled (v / 2 ^ (s + 8)) (L / 8 + 1 + 1) ha (by omega)
      simp only [setCompact, hsz, hw]
      have h3' : ¬ (L / 8 + 1 + 1 ≤ 3) := by omega
      rw [if_neg h3', Nat.shiftLeft_eq]
      have hexp : 8 * (L / 8 + 1 + 1 - 3) = s + 8 := by omega
      rw [hexp]
      have hdrop : dropBits L = s + 8 := by
        unfold dropBits; rw [if_neg hdrop_lt, if_pos hL7]; omega
      rw [hdrop]
      apply Nat.mod_eq_of_lt
      exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hv
    · simp only [if_neg hadj]
      have ha : v / 2 ^ s < 2 ^ 23 := by
        rcases Nat.lt_or_ge (v / 2 ^ s) (2 ^ 23) with hlt | hge
        · exact hlt
        · exact absurd ((adjust_iff _ hmant24).2 hge) hadj
      obtain ⟨hsz, hw, -⟩ := fields_of_assembled (v / 2 ^ s) (L / 8 + 1) ha (by omega)
      simp only [setCompact, hsz, hw]
      rw [if_neg h3, Nat.shiftLeft_eq]
      have hexp : 8 * (L / 8 + 1 - 3) = s := by omega
      rw [hexp]
      have hL7 : L % 8 ≠ 7 := by
        intro h7
        apply hadj
        apply (adjust_iff _ hmant24).2
        calc 2 ^ 23 = 2 ^ (L % 8 + 16) := by rw [h7]
          _ ≤ v / 2 ^ s := hmant_lo
      have hdrop : dropBits L = s := by
        unfold dropBits; rw [if_neg hdrop_lt, if_neg hL7]; omega
      rw [hdrop]
      apply Nat.mod_eq_of_lt
      exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hv

private theorem round_zero : setCompact (getCompact 0) = 0 := by decide

/-- The rounded value keeps the top bit of `v`. -/
private theorem round_ge_top (v : Nat) (hv0 : v ≠ 0) (hv : v < 2 ^ 256) :
    2 ^ Nat.log2 v ≤ setCompact (getCompact v) := by
  rw [round_eq v hv0 hv]
  have he := dropBits_le (Nat.log2 v)
  have hL := Nat.log2_self_le hv0
  generalize Nat.log2 v = L at *
  generalize dropBits L = e at *
  have hsplit : 2 ^ L = 2 ^ (L - e) * 2 ^ e := by rw [← Nat.pow_add]; congr 1; omega
  rw [hsplit]
  apply Nat.mul_le_mul_right
  apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2
  rw [← hsplit]; exact hL

theorem solution (v w : Nat) (hvw : v ≤ w) (hw : w < BitcoinPow.width) :
    BitcoinPow.setCompact (BitcoinPow.getCompact v) ≤ BitcoinPow.setCompact (BitcoinPow.getCompact w) := by
  by_cases hv0 : v = 0
  · subst hv0; rw [round_zero]; exact Nat.zero_le _
  have hw0 : w ≠ 0 := by omega
  have hv : v < width := Nat.lt_of_le_of_lt hvw hw
  have hLle : Nat.log2 v ≤ Nat.log2 w :=
    (Nat.le_log2 hw0).2 (Nat.le_trans (Nat.log2_self_le hv0) hvw)
  rcases Nat.lt_or_ge (Nat.log2 v) (Nat.log2 w) with hlt | hge
  · -- strictly fewer bits: everything below the top bit of w
    apply Nat.le_of_lt
    calc setCompact (getCompact v) ≤ v := BitcoinPow.getCompact_le v hv
      _ < 2 ^ (Nat.log2 v + 1) := Nat.lt_log2_self
      _ ≤ 2 ^ Nat.log2 w := Nat.pow_le_pow_right (by decide) hlt
      _ ≤ setCompact (getCompact w) := round_ge_top w hw0 hw
  · have heq : Nat.log2 v = Nat.log2 w := Nat.le_antisymm hLle hge
    rw [round_eq v hv0 hv, round_eq w hw0 hw, heq]
    exact Nat.mul_le_mul_right _ (Nat.div_le_div_right hvw)

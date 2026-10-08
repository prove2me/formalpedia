-- Prove2me | solution 1 for ExplicitExpanders.Sizes.exists_fract_mul_lt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:14:27.923797+00:00
-- url     : https://prove2.me/submissions/39c7703a-5648-4ea3-806e-d3c327e9d744

import Mathlib

set_option autoImplicit false

theorem solution {α : ℝ} (hα : Irrational α) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k₁ : ℕ, 0 < k₁ ∧ 0 < Int.fract ((k₁ : ℝ) * α) ∧ Int.fract ((k₁ : ℝ) * α) < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  obtain ⟨j, k, hk0, -, hjk⟩ := Real.exists_int_int_abs_mul_sub_le α (n := n + 1) (Nat.succ_pos n)
  have hN : (0:ℝ) < ((n + 1 : ℕ) : ℝ) + 1 := by positivity
  have hsmall : 1 / (((n + 1 : ℕ) : ℝ) + 1) < δ := by
    rw [div_lt_iff₀ hN]
    rw [div_lt_iff₀ hδ] at hn
    push_cast
    nlinarith
  have hhalf : 1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    push_cast
    have : (0:ℝ) ≤ n := by positivity
    linarith
  -- k as a natural number
  lift k to ℕ using hk0.le
  have hkpos : 0 < k := by exact_mod_cast hk0
  push_cast at hjk hsmall hhalf
  set ε : ℝ := (k : ℝ) * α - j with hε
  have hirr : ∀ m : ℕ, 0 < m → ∀ z : ℤ, (m : ℝ) * α ≠ z := by
    intro m hm z h
    exact (hα.natCast_mul (Nat.pos_iff_ne_zero.mp hm)).ne_int z h
  have hε0 : ε ≠ 0 := by
    intro h
    apply hirr k hkpos j
    linarith
  have hεle : |ε| < δ := lt_of_le_of_lt hjk hsmall
  have hεhalf : |ε| ≤ 1 / 2 := le_trans hjk hhalf
  rcases lt_or_gt_of_ne hε0 with hneg | hpos
  · -- ε < 0: let e = -ε, m = ⌊1/e⌋₊
    set e : ℝ := -ε with he
    have hepos : 0 < e := by linarith
    have heabs : e = |ε| := by rw [abs_of_neg hneg]
    set m : ℕ := ⌊1 / e⌋₊ with hm
    have h1e : 1 ≤ 1 / e := by
      rw [le_div_iff₀ hepos]; linarith
    have hm1 : 1 ≤ m := by
      rw [hm]; exact Nat.le_floor (by exact_mod_cast h1e)
    have hmle : (m : ℝ) ≤ 1 / e := Nat.floor_le (by positivity)
    have hmgt : 1 / e < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hme_le : (m : ℝ) * e ≤ 1 := by
      rw [le_div_iff₀ hepos] at hmle; linarith
    have hme_gt : 1 - e < (m : ℝ) * e := by
      rw [div_lt_iff₀ hepos] at hmgt; linarith
    have hmk : 0 < m * k := Nat.mul_pos hm1 hkpos
    have hme_ne : (m : ℝ) * e ≠ 1 := by
      intro h
      apply hirr (m * k) hmk (m * j - 1)
      push_cast
      have : (m : ℝ) * ((k : ℝ) * α - j) = -1 := by
        have : (m:ℝ) * e = (m:ℝ) * (-( (k:ℝ) * α - j)) := by rw [he, hε]
        nlinarith
      linarith
    have hme_lt : (m : ℝ) * e < 1 := lt_of_le_of_ne hme_le hme_ne
    refine ⟨m * k, hmk, ?_⟩
    have hfr : Int.fract (((m * k : ℕ) : ℝ) * α) = 1 - (m : ℝ) * e := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, m * j - 1, ?_⟩
      push_cast
      rw [he, hε]; ring
    rw [hfr]
    constructor
    · linarith
    · linarith
  · refine ⟨k, hkpos, ?_⟩
    have hfr : Int.fract ((k : ℝ) * α) = ε := by
      rw [Int.fract_eq_iff]
      rw [abs_of_pos hpos] at hεhalf
      refine ⟨hpos.le, by linarith, j, ?_⟩
      rw [hε]; ring
    rw [hfr, ← abs_of_pos hpos]
    exact ⟨abs_pos.mpr hε0, hεle⟩

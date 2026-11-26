-- Prove2me | solution 1 for ErdosDyadic.copies_meet_C
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T00:29:33.953723+00:00
-- url     : https://prove2.me/submissions/911cf08b-abeb-4e1a-9539-9eb78e29458f

import Mathlib

set_option autoImplicit false

open MeasureTheory Set

theorem solution (H : ℕ → Set ℝ)
    (hhit : ∀ j, 1 ≤ j → ∀ y : ℝ, ∀ t ∈ Icc (1 : ℝ) 2, ∃ n : ℕ, 1 ≤ n ∧
      y + t * (2 : ℝ) ^ (-(n : ℤ)) ∈ H j) :
    ∀ x s : ℝ, s ≠ 0 → ∃ N : ℕ, 1 ≤ N ∧
      x + s * (2 : ℝ) ^ (-(N : ℤ)) ∈
        ⋃ j ∈ {j : ℕ | 1 ≤ j},
          (((fun y : ℝ => (2 : ℝ) ^ (-(j : ℤ)) * y) '' H j) ∪
           ((fun y : ℝ => -((2 : ℝ) ^ (-(j : ℤ)) * y)) '' H j)) := by
  intro x s hs
  set a := |s| with ha_def
  have ha : 0 < a := abs_pos.2 hs
  set m : ℤ := Int.log 2 a with hm
  have h1 : (2:ℝ) ^ m ≤ a := Int.zpow_log_le_self (by norm_num) ha
  have h2 : a < (2:ℝ) ^ (m + 1) := Int.lt_zpow_succ_log_self (by norm_num) a
  have h2m : (0:ℝ) < 2 ^ m := zpow_pos (by norm_num) m
  set t := a / 2 ^ m with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ h2m]; linarith
  have ht2 : t ≤ 2 := by
    rw [ht, div_le_iff₀ h2m]
    have : (2:ℝ) ^ (m + 1) = 2 ^ m * 2 := by rw [zpow_add_one₀ (by norm_num)]
    nlinarith
  set j : ℕ := (-m).toNat + 1 with hj
  have hj1 : 1 ≤ j := by omega
  have hmj : 0 ≤ m + j := by omega
  have key : ∀ y : ℝ, ∀ n : ℕ, ((2:ℝ) ^ (-(j:ℤ))) * (y + t * 2 ^ (-(n:ℤ))) =
      2 ^ (-(j:ℤ)) * y + a * 2 ^ (-(((m + j).toNat + n : ℕ) : ℤ)) := by
    intro y n
    have e : (((m + j).toNat + n : ℕ) : ℤ) = m + j + n := by push_cast; omega
    rw [e, ht, mul_add]
    congr 1
    have : -(m + (j:ℤ) + n) = -m + (-(j:ℤ)) + (-(n:ℤ)) := by ring
    rw [this, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num), zpow_neg (2:ℝ) m]
    field_simp
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · obtain ⟨n, hn, hmem⟩ := hhit j hj1 (-(2 ^ (j:ℤ) * x)) t ⟨ht1, ht2⟩
    refine ⟨(m + j).toNat + n, by omega, ?_⟩
    simp only [mem_iUnion, mem_setOf_eq, mem_union, mem_image]
    refine ⟨j, hj1, Or.inr ⟨_, hmem, ?_⟩⟩
    rw [key]
    have : (2:ℝ) ^ (-(j:ℤ)) * (-(2 ^ (j:ℤ) * x)) = -x := by
      rw [zpow_neg]; field_simp
    rw [this, ha_def, abs_of_neg hneg]; ring
  · obtain ⟨n, hn, hmem⟩ := hhit j hj1 (2 ^ (j:ℤ) * x) t ⟨ht1, ht2⟩
    refine ⟨(m + j).toNat + n, by omega, ?_⟩
    simp only [mem_iUnion, mem_setOf_eq, mem_union, mem_image]
    refine ⟨j, hj1, Or.inl ⟨_, hmem, ?_⟩⟩
    rw [key]
    have : (2:ℝ) ^ (-(j:ℤ)) * (2 ^ (j:ℤ) * x) = x := by
      rw [zpow_neg]; field_simp
    rw [this, ha_def, abs_of_pos hpos]

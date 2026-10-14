-- Prove2me | solution 1 for CycleLengthsExp.ManyLengths.k_bound
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-12T11:23:45.025629+00:00
-- url     : https://prove2.me/submissions/5c6c0ca0-acd8-4389-a93c-37291ea8a723

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

set_option autoImplicit false

open CycleLengthsExp.ManyLengths

/-- Friedman–Krivelevich, Cycle lengths in expanding graphs, p. 13, proof of
Theorem 2: the explicitly chosen integer `k(α) = 2⌈log₂(3/α)/log₂(1+α/2)⌉+1`
satisfies `k(α) ≤ K * log₂(2/α)/α` for an absolute constant `K > 0`,
uniformly for `0 < α ≤ 1`.

Proof idea: `⌈x⌉ ≤ x+1`; `log₂(3/α) ≤ 2*log₂(2/α)` (as `3/α ≤ (2/α)²`
for `α ≤ 1`); `log₂(1+α/2) ≥ α/(3*log 2)` (from `log(1+t) ≥ t/(1+t)`);
absorbing the `+3` constant via `log₂(2/α)/α ≥ 1`. Witness:
`K = 12*log 2 + 3`.

`solution` is top-level (the verifier looks up unqualified `solution`);
`CycleLengthsExp.ManyLengths.k_bound` below is the ascribed alias matching
the published node name. -/
theorem solution : ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    (kNum α : ℝ) ≤ K * Real.logb 2 (2 / α) / α := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨12 * Real.log 2 + 3, by linarith, fun α hα0 hα1 => ?_⟩
  have hαne : α ≠ 0 := ne_of_gt hα0
  have hlogne : Real.log 2 ≠ 0 := ne_of_gt hlog2
  -- (i) L := logb 2 (2/α) ≥ 1
  have hL1 : (1:ℝ) ≤ Real.logb 2 (2 / α) := by
    have h2 : (2:ℝ) ≤ 2 / α := by
      rw [le_div_iff₀ hα0]
      linarith [hα1]
    calc (1:ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ Real.logb 2 (2 / α) :=
          Real.logb_le_logb_of_le (by norm_num) (by norm_num) h2
  -- (ii) numerator: logb 2 (3/α) ≤ 2 * logb 2 (2/α)
  have hnum : Real.logb 2 (3 / α) ≤ 2 * Real.logb 2 (2 / α) := by
    have h3α : (3:ℝ) / α ≤ (2 / α) ^ 2 := by
      have hαsq : (0:ℝ) < α ^ 2 := by positivity
      have e1 : (3:ℝ) / α = (3 * α) / (α ^ 2) := by
        field_simp
      have e2 : ((2:ℝ) / α) ^ 2 = 4 / (α ^ 2) := by
        field_simp
        ring
      rw [e1, e2, div_le_div_iff_of_pos_right hαsq]
      linarith [hα1]
    have h3αpos : (0:ℝ) < 3 / α := div_pos (by norm_num) hα0
    calc Real.logb 2 (3 / α) ≤ Real.logb 2 ((2 / α) ^ 2) :=
            Real.logb_le_logb_of_le (by norm_num) h3αpos h3α
      _ = 2 * Real.logb 2 (2 / α) := by
            simp only [Real.logb_pow, Nat.cast_ofNat]
  -- (iii) denominator: logb 2 (1+α/2) ≥ α / (3 * log 2)
  have hden : α / (3 * Real.log 2) ≤ Real.logb 2 (1 + α / 2) := by
    have hpos : (0:ℝ) < 1 + α / 2 := by linarith
    have h1ln : (α / 3 : ℝ) ≤ Real.log (1 + α / 2) := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
      rw [Real.log_inv] at h
      have h2 : (1:ℝ) - (1 + α / 2)⁻¹ ≤ Real.log (1 + α / 2) := by linarith
      have hne : ((1:ℝ) + α / 2) ≠ 0 := ne_of_gt hpos
      have e : (1:ℝ) - (1 + α / 2)⁻¹ = (α / 2) / (1 + α / 2) := by
        rw [inv_eq_one_div]
        field_simp
        ring
      have hα2 : α ^ 2 ≤ α := by
        have h := mul_le_mul_of_nonneg_left hα1 (le_of_lt hα0)
        rw [mul_one] at h
        have e2 : α ^ 2 = α * α := by ring
        rw [e2]; exact h
      have h3 : (α / 3 : ℝ) ≤ (α / 2) / (1 + α / 2) := by
        rw [le_div_iff₀ hpos]
        have e : (α / 3) * (1 + α / 2) = α / 2 - (α - α ^ 2) / 6 := by ring
        rw [e]
        have hnn : (0:ℝ) ≤ (α - α ^ 2) / 6 :=
          div_nonneg (by linarith [hα2]) (by norm_num)
        linarith
      rw [e] at h2
      exact h3.trans h2
    have hlogb_eq : Real.logb 2 (1 + α / 2)
        = Real.log (1 + α / 2) / Real.log 2 := rfl
    have h3' : (α / 3 : ℝ) / Real.log 2
        ≤ Real.log (1 + α / 2) / Real.log 2 :=
      (div_le_div_iff_of_pos_right hlog2).mpr h1ln
    have eα : α / (3 * Real.log 2) = (α / 3) / Real.log 2 := by ring
    rw [hlogb_eq, eα]
    exact h3'
  have hdenpos : (0:ℝ) < Real.logb 2 (1 + α / 2) := by
    have hα3 : (0:ℝ) < α / (3 * Real.log 2) :=
      div_pos hα0 (mul_pos (by norm_num) hlog2)
    exact lt_of_lt_of_le hα3 hden
  -- (iv) the ratio A := logb 2 (3/α) / logb 2 (1+α/2) ≤ 6 * log 2 * L / α
  have hA : Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)
      ≤ 6 * Real.log 2 * Real.logb 2 (2 / α) / α := by
    rw [div_le_iff₀ hdenpos]
    have hnn : (0:ℝ) ≤ 6 * Real.log 2 * Real.logb 2 (2 / α) / α :=
      div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hlog2))
          (le_trans (by norm_num) hL1)) (le_of_lt hα0)
    have hmul := mul_le_mul_of_nonneg_left hden hnn
    have h3logne : (3:ℝ) * Real.log 2 ≠ 0 := mul_ne_zero (by norm_num) hlogne
    have eR : (6 * Real.log 2 * Real.logb 2 (2 / α) / α) * (α / (3 * Real.log 2))
        = 2 * Real.logb 2 (2 / α) := by
      field_simp
      ring
    rw [eR] at hmul
    calc Real.logb 2 (3 / α) ≤ 2 * Real.logb 2 (2 / α) := hnum
      _ ≤ (6 * Real.log 2 * Real.logb 2 (2 / α) / α)
          * Real.logb 2 (1 + α / 2) := hmul
  -- (v) ceil: ↑⌈A⌉₊ ≤ A + 1
  have hA0 : (0:ℝ) ≤ Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2) :=
    div_nonneg
      (Real.logb_nonneg (by norm_num) (by
        rw [le_div_iff₀ hα0]
        linarith [hα1]))
      (le_of_lt hdenpos)
  have hceil : ((Nat.ceil (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) : ℕ) : ℝ)
      ≤ Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2) + 1 :=
    (Nat.ceil_lt_add_one hA0).le
  -- (vi) absorb the +3 via logb 2 (2/α) / α ≥ 1
  have hM : (1:ℝ) ≤ Real.logb 2 (2 / α) / α := by
    rw [le_div_iff₀ hα0]
    linarith [hL1, hα1]
  -- assembly
  unfold kNum
  push_cast
  have step1 : (2 * ((Nat.ceil (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) : ℕ) : ℝ) + 1)
      ≤ 2 * (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) + 3 := by
    have h1 := mul_le_mul_of_nonneg_left hceil (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have step2 : (2 * (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) + 3)
      ≤ 2 * (6 * Real.log 2 * Real.logb 2 (2 / α) / α) + 3 := by
    have h2 := mul_le_mul_of_nonneg_left hA (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have step3 : (2 * (6 * Real.log 2 * Real.logb 2 (2 / α) / α) + 3)
      ≤ (12 * Real.log 2 + 3) * (Real.logb 2 (2 / α) / α) := by
    have h3M : (3:ℝ) ≤ 3 * (Real.logb 2 (2 / α) / α) := by linarith [hM]
    have e2 : (12 * Real.log 2 + 3) * (Real.logb 2 (2 / α) / α)
        = 12 * Real.log 2 * (Real.logb 2 (2 / α) / α)
          + 3 * (Real.logb 2 (2 / α) / α) := by ring
    rw [e2]
    have key : (2:ℝ) * (6 * Real.log 2 * Real.logb 2 (2 / α) / α) + 3
        ≤ 12 * Real.log 2 * (Real.logb 2 (2 / α) / α)
          + 3 * (Real.logb 2 (2 / α) / α) := by
      have ering : (2:ℝ) * (6 * Real.log 2 * Real.logb 2 (2 / α) / α)
          = 12 * Real.log 2 * (Real.logb 2 (2 / α) / α) := by ring
      rw [ering]
      have hle := add_le_add_right h3M
        (12 * Real.log 2 * (Real.logb 2 (2 / α) / α))
      linarith
    exact key
  calc (2 * ((Nat.ceil (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) : ℕ) : ℝ) + 1)
        ≤ 2 * (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) + 3 := step1
      _ ≤ 2 * (6 * Real.log 2 * Real.logb 2 (2 / α) / α) + 3 := step2
      _ ≤ (12 * Real.log 2 + 3) * (Real.logb 2 (2 / α) / α) := step3
      _ = (12 * Real.log 2 + 3) * Real.logb 2 (2 / α) / α := by ring

-- Dual-named alias: the platform looks up `CycleLengthsExp.ManyLengths.k_bound`.
namespace CycleLengthsExp.ManyLengths

theorem k_bound : ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    (kNum α : ℝ) ≤ K * Real.logb 2 (2 / α) / α := _root_.solution

end CycleLengthsExp.ManyLengths

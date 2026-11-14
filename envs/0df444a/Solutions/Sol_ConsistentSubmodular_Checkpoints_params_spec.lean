-- Prove2me | solution 1 for ConsistentSubmodular.Checkpoints.params_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:49.514198+00:00
-- url     : https://prove2.me/submissions/c9c26751-ff41-4d13-8acc-69f2a9785ee2

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_Checkpoints

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints

theorem solution {γ : ℝ} (hγ : 0 < γ) (hγ8 : γ < 1 / 8) {k : ℕ}
    (hk : 8 / γ ^ 2 ≤ k) :
    (params γ k).Valid k ∧ 2 * (params γ k).s + 1 ≤ consistency γ ∧
      1 / ((params γ k).h : ℝ) ≤ γ ∧ 1 - 2 * γ ≤ ((params γ k).κ : ℝ) / k := by
  have hinv : 8 < 1 / γ := by rw [lt_one_div (by norm_num) hγ]; linarith
  have hγ2 : 0 < γ ^ 2 := by positivity
  have hkγ : 8 ≤ γ ^ 2 * k := by rwa [div_le_iff₀ hγ2, mul_comm] at hk
  have hkpos : (0 : ℝ) < k := by nlinarith
  set x := γ * k with hx
  have hx64 : 64 ≤ x := by
    have : γ * (1 / γ) = 1 := by field_simp
    nlinarith
  -- `ℓ = ⌊γk⌋`
  set ℓ := ⌊x⌋₊ with hℓ
  have hℓle : (ℓ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hℓgt : x < ℓ + 1 := Nat.lt_floor_add_one x
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < ℓ := by linarith
    exact_mod_cast this
  -- `h = ⌈1/γ⌉`
  set h := ⌈1 / γ⌉₊ with hh
  have hhge : 1 / γ ≤ h := Nat.le_ceil _
  have hhlt : (h : ℝ) < 1 / γ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hhpos : 0 < h := by
    have : (0 : ℝ) < h := by linarith
    exact_mod_cast this
  have hhγ : (h : ℝ) * γ < 2 := by
    have : (1 / γ + 1) * γ = 1 + γ := by field_simp
    nlinarith
  -- `d = ⌊ℓ/h⌋ ≥ γ²k/8`
  set d := ℓ / h with hd
  have hdiv : ℓ < d * h + h := Nat.lt_div_mul_add hhpos
  have hdivR : (ℓ : ℝ) < (d + 1) * h := by
    have : ((ℓ : ℕ) : ℝ) < ((d * h + h : ℕ) : ℝ) := by exact_mod_cast hdiv
    push_cast at this
    linarith
  have hdγ : γ ^ 2 * k / 8 ≤ d := by
    -- `(d + 1) · 2 > (d + 1) h γ > ℓ γ > γ x / 2`
    have h1 : (ℓ : ℝ) * γ < (d + 1) * (h * γ) := by nlinarith
    have h2 : (d + 1) * (h * γ) ≤ (d + 1) * 2 := by
      apply mul_le_mul_of_nonneg_left hhγ.le
      positivity
    have h3 : x / 2 * γ ≤ ℓ * γ := by nlinarith
    have h4 : x * γ = γ ^ 2 * k := by rw [hx]; ring
    nlinarith
  have hdpos : 0 < d := by
    have : (0 : ℝ) < d := by nlinarith
    exact_mod_cast this
  -- `s = ⌊k/d⌋ + 1`
  have hsd : k ≤ (k / d + 1) * d := by
    have := Nat.lt_div_mul_add (a := k) hdpos
    rw [add_one_mul]
    omega
  have hkd : (k : ℝ) / d ≤ 8 / γ ^ 2 := by
    rw [div_le_div_iff₀ (by exact_mod_cast hdpos) hγ2]
    nlinarith
  have hs : ((k / d : ℕ) : ℝ) ≤ 8 / γ ^ 2 := (Nat.cast_div_le).trans hkd
  have hcons : 2 * (k / d + 1) + 1 ≤ consistency γ := by
    have hc := Nat.le_ceil (16 / γ ^ 2)
    have h16 : 16 / γ ^ 2 = 2 * (8 / γ ^ 2) := by ring
    have : ((2 * (k / d + 1) + 1 : ℕ) : ℝ) ≤ ((consistency γ : ℕ) : ℝ) := by
      unfold consistency
      push_cast
      linarith
    exact_mod_cast this
  -- `2ℓ ≤ k`
  have h2ℓ : 2 * ℓ ≤ k := by
    have : (2 * ℓ : ℝ) ≤ k := by nlinarith
    exact_mod_cast this
  refine ⟨⟨hℓpos, hhpos, ?_, hsd⟩, hcons, ?_, ?_⟩
  · show k - 2 * ℓ + 2 * ℓ ≤ k
    omega
  · show 1 / (h : ℝ) ≤ γ
    rw [div_le_iff₀ (by exact_mod_cast hhpos)]
    have : γ * (1 / γ) = 1 := by field_simp
    nlinarith
  · show 1 - 2 * γ ≤ ((k - 2 * ℓ : ℕ) : ℝ) / k
    rw [Nat.cast_sub h2ℓ, le_div_iff₀ hkpos]
    push_cast
    nlinarith

end

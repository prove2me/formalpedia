-- Prove2me | solution 1 for BirkhoffGlobalSection.noncollinear_critical_unit_distances
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T22:39:31.537987+00:00
-- url     : https://prove2.me/submissions/fca0ca8f-ef9a-4400-946d-0c17efb781b6

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Theorems.Thm_BirkhoffGlobalSection_noncollinear_critical_equal_primary_distances
import Theorems.Thm_BirkhoffGlobalSection_noncollinear_critical_vertical_balance

open BirkhoffGlobalSection

theorem solution (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (s : Phase)
    (hfree : collisionFree μ s)
    (hcrit : isCriticalPoint (jacobiHamiltonian μ) s)
    (hoffaxis : s 1 ≠ 0) :
    (s 0 + μ) ^ 2 + (s 1) ^ 2 = 1 ∧
      (s 0 - 1 + μ) ^ 2 + (s 1) ^ 2 = 1 := by
  let d₁ : ℝ := (s 0 + μ) ^ 2 + (s 1) ^ 2
  let d₂ : ℝ := (s 0 - 1 + μ) ^ 2 + (s 1) ^ 2
  have heq : d₁ = d₂ :=
    noncollinear_critical_equal_primary_distances μ hμ0 hμ1 s hfree hcrit hoffaxis
  have hbalance : (1 - μ) / (Real.sqrt d₁) ^ 3 +
      μ / (Real.sqrt d₂) ^ 3 = 1 :=
    noncollinear_critical_vertical_balance μ hμ0 hμ1 s hfree hcrit hoffaxis
  rw [← heq] at hbalance
  have hpos : 0 < (Real.sqrt d₁) ^ 3 :=
    pow_pos (Real.sqrt_pos.2 hfree.1) 3
  have hinv : 1 / (Real.sqrt d₁) ^ 3 = 1 := by
    calc
      1 / (Real.sqrt d₁) ^ 3 = ((1 - μ) + μ) / (Real.sqrt d₁) ^ 3 := by ring
      _ = 1 := by rw [add_div]; exact hbalance
  have hcube : (Real.sqrt d₁) ^ 3 = 1 := by
    have h := (div_eq_iff (ne_of_gt hpos)).mp hinv
    simpa using h.symm
  have hsqrt : Real.sqrt d₁ = 1 := by
    apply (pow_left_inj₀ (Real.sqrt_nonneg d₁)
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (3 : ℕ) ≠ 0)).mp
    simpa using hcube
  have hd₁ : d₁ = 1 := Real.sqrt_eq_one.mp hsqrt
  have hd₂ : d₂ = 1 := heq.symm.trans hd₁
  exact ⟨hd₁, hd₂⟩

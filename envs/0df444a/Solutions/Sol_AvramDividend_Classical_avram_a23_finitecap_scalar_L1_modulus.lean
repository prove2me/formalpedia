-- Prove2me | solution 1 for AvramDividend.Classical.avram_a23_finitecap_scalar_L1_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:45:49.512194+00:00
-- url     : https://prove2.me/submissions/6521bd7e-c1ad-4828-b788-f3acb08f68a0

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
open Set

theorem solution
    (w : ℝ → ℝ) (b K ε δ : ℝ)
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hbound : ∀ y : ℝ, y ∈ Icc 0 b → |w y| ≤ K)
    (hmod : ∀ y ∈ Icc 0 b, ∀ z ∈ Icc 0 b,
      |y-z| < δ → |w y-w z| ≤ ε)
    (y z : ℝ) (hy : y ∈ Icc 0 b) (hz : z ∈ Icc 0 b) :
    |w y - w z| ≤ ε + (2*K/δ) * |y-z|  := by
  have hcoef : 0 ≤ 2 * K / δ := div_nonneg (by linarith) (le_of_lt hδ)
  have hnon : 0 ≤ |y-z| := abs_nonneg _
  by_cases hnear : |y-z| < δ
  · have hm := hmod y hy z hz hnear
    nlinarith [mul_nonneg hcoef hnon]
  · have hfar : δ ≤ |y-z| := le_of_not_gt hnear
    have hTri : |w y - w z| ≤ |w y| + |w z| := by
      simpa using (abs_sub_le (w y) 0 (w z))
    have hBound : |w y - w z| ≤ 2*K := by
      have hY := hbound y hy
      have hZ := hbound z hz
      linarith
    have hSloped : 2*K ≤ (2*K/δ)*|y-z| := by
      have heq : (2*K/δ)*δ = 2*K := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_left hfar hcoef]
    linarith

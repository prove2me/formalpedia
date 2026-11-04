-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_negative_levy_near_far_kernel_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:30:59.097819+00:00
-- url     : https://prove2.me/submissions/5a5cdca3-5ef9-4cdd-9823-94c726c75ca3

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical
noncomputable section

/-- The genuine BV negative-jump kernel has a Lipschitz small-jump bound and a bounded far-tail bound on each compact positive reserve band. -/
theorem solution (w : ℝ → ℝ)
  (a b L R : ℝ) (ha : 0 < a) (hab : a ≤ b)
  (hL : 0 ≤ L) (hR : 0 ≤ R)
  (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
    |w u - w v| ≤ L * |u - v|)
  (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
  (y z : ℝ) (hy : y ∈ Icc a b) (hz : z < 0) :
  ((-a / 2 < z → |w (y + z) - w y| ≤ L * |z|) ∧
   (z ≤ -a / 2 → |w (y + z) - w y| ≤ 2 * R)) := by
  rcases hy with ⟨hya, hyb⟩
  constructor
  · intro hNear
    have hyIn : y ∈ Icc (a / 2) b := ⟨by linarith, hyb⟩
    have hyzIn : y + z ∈ Icc (a / 2) b := by
      constructor <;> linarith
    have h := hLip (y + z) hyzIn y hyIn
    have hsub : y + z - y = z := by ring
    simpa [hsub] using h
  · intro hFar
    have hyz_le : y + z ≤ b := by linarith
    have h1 := hWbound (y + z) hyz_le
    have h2 := hWbound y hyb
    have h3 := abs_sub (w (y + z)) (w y)
    linarith

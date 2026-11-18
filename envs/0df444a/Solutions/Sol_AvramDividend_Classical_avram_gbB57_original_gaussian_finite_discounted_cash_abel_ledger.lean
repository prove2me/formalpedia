-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB57_original_gaussian_finite_discounted_cash_abel_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:45:10.219289+00:00
-- url     : https://prove2.me/submissions/6c341ada-4df5-4106-9c04-b58251f31561

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB53_physical_discounted_mesh_abel_telescope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section
/-- Exact finite discounted risk-reserve, dividend-cash and Gaussian-noise ledger. -/
theorem solution
    (m : ℕ) (a B s D : ℕ → ℝ) (C : ℝ) (w : ℝ → ℝ) :
    let Y : ℕ → ℝ := fun i => C + B i + 2 * s i - D i
    a m * w (Y (m + 1)) +
      (Finset.range (m + 1)).sum (fun i => a i * (D (i + 1) - D i)) -
      a 0 * w (Y 0) -
      (Finset.range (m + 1)).sum (fun i => a i * (B (i + 1) - B i)) =
    a m * (w (Y (m + 1)) - Y (m + 1)) +
      a 0 * (Y 0 - w (Y 0)) +
      2 * (Finset.range (m + 1)).sum (fun i => a i * (s (i + 1) - s i)) -
      (Finset.range m).sum (fun i => (a i - a (i + 1)) * Y (i + 1))
    := by
  dsimp
  let Y : ℕ → ℝ := fun i => C + B i + 2 * s i - D i
  have hCell (i : ℕ) :
      a i * (D (i + 1) - D i) -
      a i * (B (i + 1) - B i) =
      2 * a i * (s (i + 1) - s i) -
      a i * (Y (i + 1) - Y i) := by
    dsimp [Y]
    ring
  have hSum :
      (Finset.range (m + 1)).sum (fun i => a i * (D (i + 1) - D i)) -
      (Finset.range (m + 1)).sum (fun i => a i * (B (i + 1) - B i)) =
      2 * (Finset.range (m + 1)).sum (fun i => a i * (s (i + 1) - s i)) -
      (Finset.range (m + 1)).sum (fun i => a i * (Y (i + 1) - Y i)) := by
    calc
      _ = (Finset.range (m + 1)).sum (fun i =>
          a i * (D (i + 1) - D i) -
            a i * (B (i + 1) - B i)) := by
        rw [Finset.sum_sub_distrib]
      _ = (Finset.range (m + 1)).sum (fun i =>
          2 * a i * (s (i + 1) - s i) -
            a i * (Y (i + 1) - Y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hCell i
      _ = _ := by
        rw [Finset.sum_sub_distrib]
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]
  have hAbel :=
    avram_gbB53_physical_discounted_mesh_abel_telescope m a Y
  change a m * w (Y (m + 1)) +
      (Finset.range (m + 1)).sum (fun i => a i * (D (i + 1) - D i)) -
      a 0 * w (Y 0) -
      (Finset.range (m + 1)).sum (fun i => a i * (B (i + 1) - B i)) =
    a m * (w (Y (m + 1)) - Y (m + 1)) +
      a 0 * (Y 0 - w (Y 0)) +
      2 * (Finset.range (m + 1)).sum (fun i => a i * (s (i + 1) - s i)) -
      (Finset.range m).sum (fun i => (a i - a (i + 1)) * Y (i + 1))
  linear_combination hSum - hAbel

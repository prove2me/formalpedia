-- Prove2me | solution 1 for AvramDividend.Classical.derivZeroPlus_pos_of_excursion_and_W0
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T18:11:36.518993+00:00
-- url     : https://prove2.me/submissions/f8769682-c55b-4e6b-84ed-f0b15cb47aee

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_deriv_global_lower_le_right_liminf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution
    (W : ℝ → ℝ) (φ : ℝ) (μ : Measure ℝ)
    (hφ : 0 < φ) (hW0 : 0 < W 0)
    (hmono : MonotoneOn W (Ici 0))
    (hrepr : ∀ x : ℝ, 0 < x →
      deriv W x = W x * (φ + μ.real (Ici x))) :
    (0 : EReal) < derivZeroPlus W := by
  let d : ℝ := φ * W 0
  have hd : 0 < d := by
    dsimp [d]
    exact mul_pos hφ hW0
  have hlower : ∀ x : ℝ, 0 < x → d ≤ deriv W x := by
    intro x hx
    have hWx : W 0 ≤ W x :=
      hmono (by simp) (by exact hx.le) hx.le
    have hWx0 : 0 ≤ W x :=
      le_trans hW0.le hWx
    have htail : 0 ≤ μ.real (Ici x) := measureReal_nonneg
    rw [hrepr x hx]
    dsimp [d]
    have h1 : φ * W 0 ≤ φ * W x :=
      mul_le_mul_of_nonneg_left hWx hφ.le
    have h2 : φ * W x ≤ W x * (φ + μ.real (Ici x)) := by
      nlinarith [mul_nonneg hWx0 htail]
    nlinarith
  have hlim :
      ((d : ℝ) : EReal) ≤ derivZeroPlus W :=
    deriv_global_lower_le_right_liminf W d hlower
  have hdE : (0 : EReal) < ((d : ℝ) : EReal) := by
    exact_mod_cast hd
  exact lt_of_lt_of_le hdE hlim

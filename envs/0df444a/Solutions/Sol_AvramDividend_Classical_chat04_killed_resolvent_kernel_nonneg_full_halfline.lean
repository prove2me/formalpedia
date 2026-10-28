-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_resolvent_kernel_nonneg_full_halfline
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:34:47.161205+00:00
-- url     : https://prove2.me/submissions/175d8c1e-a8e4-4501-837c-22eb6d238253

import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_kernel_nonneg_of_tilted_monotone_interior

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Real Set

/-- Positivity of the killed-resolvent density on the entire spatial half-line. -/
theorem solution
    (θ : ℝ) (W : ℝ → ℝ)
    (hmono : MonotoneOn (fun z : ℝ => Real.exp (-(θ * z)) * W z) (Ici (0 : ℝ)))
    (hpos : ∀ z : ℝ, 0 ≤ z → 0 ≤ W z)
    (hnegative : ∀ z : ℝ, z < 0 → W z = 0)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ Real.exp (-(θ * y)) * W x - W (x - y) := by
  by_cases hxy : y ≤ x
  · exact chat04_killed_resolvent_kernel_nonneg_of_tilted_monotone_interior
      θ W hmono x y hx hy hxy
  · have hbelow : x - y < 0 := by linarith
    rw [hnegative (x - y) hbelow]
    simp only [sub_zero]
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hpos x hx)

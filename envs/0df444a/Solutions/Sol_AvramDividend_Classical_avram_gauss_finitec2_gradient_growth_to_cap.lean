-- Prove2me | solution 1 for AvramDividend.Classical.avram_gauss_finitec2_gradient_growth_to_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:49:56.607483+00:00
-- url     : https://prove2.me/submissions/ccbbc891-4e29-4cad-8dd7-0b97544b8f5d

import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

/-- The dividend-gradient lower bound makes value minus reserve
    monotone, including the finite top-cap endpoint by continuity. -/
theorem solution
    (w : ℝ → ℝ) (u C : ℝ) (huC : u < C)
    (hwcont : ContinuousOn w (Icc u C))
    (hwderiv : ∀ y ∈ Ioo u C, HasDerivAt w (deriv w y) y)
    (hgrad : ∀ y ∈ Ioo u C, 1 ≤ deriv w y) :
    ∀ t ∈ Icc u C, C - t ≤ w C - w t := by
  have hcont : ContinuousOn (fun y : ℝ => w y - y) (Icc u C) :=
    hwcont.sub continuous_id.continuousOn
  have hd : ∀ y ∈ interior (Icc u C),
      HasDerivWithinAt (fun z : ℝ => w z - z)
        (deriv w y - 1) (interior (Icc u C)) y := by
    intro y hy
    have hy' : y ∈ Ioo u C := by simpa using hy
    exact ((hwderiv y hy').sub (hasDerivAt_id y)).hasDerivWithinAt
  have hnonneg : ∀ y ∈ interior (Icc u C), 0 ≤ deriv w y - 1 := by
    intro y hy
    have hy' : y ∈ Ioo u C := by simpa using hy
    exact sub_nonneg.mpr (hgrad y hy')
  have hm : MonotoneOn (fun y : ℝ => w y - y) (Icc u C) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc u C) hcont hd hnonneg
  intro t ht
  have hle := hm ht ⟨huC.le, le_rfl⟩ ht.2
  dsimp at hle
  linarith

-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger29_topcap_secant_without_contdiff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:43:31.536199+00:00
-- url     : https://prove2.me/submissions/9052001d-3ab4-4777-b428-4d5894dc3383

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

/-- A positive pointwise derivative forces the reward minus identity to
    be monotone, without continuity of the derivative. -/
theorem solution (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_grad : ∀ y : ℝ, 0 < y → 1 ≤ deriv w y)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    b - a ≤ w b - w a := by
  let g : ℝ → ℝ := fun y => w y - y
  have hgcont : ContinuousOn g (Ici 0) :=
    hw_cont.sub continuousOn_id
  have hwdiff (y : ℝ) (hy : 0 < y) : DifferentiableAt ℝ w y := by
    apply differentiableAt_of_deriv_ne_zero
    linarith [hw_grad y hy]
  have hgdiff : DifferentiableOn ℝ g (interior (Ici (0 : ℝ))) := by
    intro y hy
    have hy0 : 0 < y := by
      simpa only [interior_Ici, mem_Ioi] using hy
    exact ((hwdiff y hy0).sub differentiableAt_id).differentiableWithinAt
  have hgderiv :
      ∀ y ∈ interior (Ici (0 : ℝ)), 0 ≤ deriv g y := by
    intro y hy
    have hy0 : 0 < y := by
      simpa only [interior_Ici, mem_Ioi] using hy
    have hh : HasDerivAt g (deriv w y - 1) y := by
      exact (hwdiff y hy0).hasDerivAt.sub (hasDerivAt_id y)
    rw [hh.deriv]
    linarith [hw_grad y hy0]
  have hmono : MonotoneOn g (Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hgcont hgdiff hgderiv
  have hh : g a ≤ g b := hmono ha (ha.trans hab) hab
  dsimp only [g] at hh
  linarith

-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledCappedClipped_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/fd38689c-9440-46d8-a9f0-3aa96ba923ef

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrable
import Theorems.Thm_CohnElkies_integral_stripPoissonKernel
import Theorems.Thm_CohnElkies_lowerGammaScaledCappedClipped_eq_lowerClip_add
import Theorems.Thm_CohnElkies_lowerGammaScaledCappedLowerClip_poisson_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) {c D n σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
      lowerGammaScaledCappedClipped d c D n Y) =
      (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
        lowerGammaScaledCappedLowerClip d c D n Y) +
          n * stripBottomMass σ := by
  have hclip :=
    lowerGammaScaledCappedLowerClip_poisson_integrable
      hd (c := c) (D := D) (n := n)
      hbelow habove s
  have hk := (stripPoissonKernel_integrable
    hbelow habove).comp_sub_left s
  have hnkernel := hk.const_mul n
  calc
    (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
      lowerGammaScaledCappedClipped d c D n Y) =
        ∫ Y : ℝ,
          (stripPoissonKernel σ (s - Y) *
            lowerGammaScaledCappedLowerClip d c D n Y) +
          n * stripPoissonKernel σ (s - Y) := by
      apply integral_congr_ae
      filter_upwards [] with Y
      rw [lowerGammaScaledCappedClipped_eq_lowerClip_add]
      ring
    _ =
        (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
          lowerGammaScaledCappedLowerClip d c D n Y) +
        ∫ Y : ℝ, n * stripPoissonKernel σ (s - Y) :=
      integral_add hclip hnkernel
    _ =
        (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
          lowerGammaScaledCappedLowerClip d c D n Y) +
        n * ∫ Y : ℝ, stripPoissonKernel σ (s - Y) := by
      rw [integral_const_mul]
    _ =
        (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
          lowerGammaScaledCappedLowerClip d c D n Y) +
        n * stripBottomMass σ := by
      rw [integral_sub_left_eq_self
        (stripPoissonKernel σ) volume s,
        integral_stripPoissonKernel hbelow habove]
end CohnElkies

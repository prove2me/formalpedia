-- Prove2me | solution 1 for CohnElkies.saddleSourceCenteredEnvelope_stationary_gaussian_error_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/5d540d25-0d8e-4ea0-9644-7cfa41206547

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceCenteredPhase_cubic_remainder_norm_le
import Theorems.Thm_CohnElkies_saddleSourceCenteredEnvelope_stationary_eq_exp_phase
import Theorems.Thm_CohnElkies_exp_saddleSourceCenteredPhase_eq_gaussian_mul

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 < ℓ)
    (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    (T : ℝ)
    (hsmall :
      (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 ≤ 1) :
    ‖saddleSourceCenteredEnvelope ε ℓ u
        (saddleSourceStationaryLogRadius ε ℓ u) T -
      (saddleSourceGaussianKernel ε ℓ u T : ℂ)‖ ≤
      2 * saddleSourceGaussianKernel ε ℓ u T *
        ((ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
          |T| ^ 3) := by
  let R : ℂ := saddleSourceGaussianPhaseRemainder ε ℓ u T
  let q : ℝ :=
    (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
      |T| ^ 3
  have hR : ‖R‖ ≤ q := by
    exact saddleSourceCenteredPhase_cubic_remainder_norm_le
      hε hℓ hu horder hmargin T
  have hRone : ‖R‖ ≤ 1 := hR.trans hsmall
  have hg : 0 < saddleSourceGaussianKernel ε ℓ u T := by
    unfold saddleSourceGaussianKernel
    exact Real.exp_pos _
  rw [saddleSourceCenteredEnvelope_stationary_eq_exp_phase
    hℓ hu T,
    exp_saddleSourceCenteredPhase_eq_gaussian_mul]
  have hfactor :
      (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
          Complex.exp R -
        (saddleSourceGaussianKernel ε ℓ u T : ℂ) =
      (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
        (Complex.exp R - 1) := by
    ring
  change
    ‖(saddleSourceGaussianKernel ε ℓ u T : ℂ) *
          Complex.exp R -
        (saddleSourceGaussianKernel ε ℓ u T : ℂ)‖ ≤
      2 * saddleSourceGaussianKernel ε ℓ u T * q
  rw [hfactor, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hg]
  calc
    saddleSourceGaussianKernel ε ℓ u T *
        ‖Complex.exp R - 1‖ ≤
      saddleSourceGaussianKernel ε ℓ u T *
        (2 * ‖R‖) :=
      mul_le_mul_of_nonneg_left
        (Complex.norm_exp_sub_one_le hRone) hg.le
    _ ≤ saddleSourceGaussianKernel ε ℓ u T *
        (2 * q) := by
      gcongr
    _ = 2 * saddleSourceGaussianKernel ε ℓ u T * q := by
      ring
end CohnElkies

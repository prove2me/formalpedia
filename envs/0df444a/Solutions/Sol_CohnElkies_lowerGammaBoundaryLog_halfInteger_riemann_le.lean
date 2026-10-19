-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_halfInteger_riemann_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/9b2d7b0e-863b-4d5e-831d-662a4f0928f3

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerCoth_log_antitoneOn
import Theorems.Thm_CohnElkies_lowerRiemannLog_monotoneOn
import Theorems.Thm_CohnElkies_lower_halfInteger_midpointRiemann_error
import Theorems.Thm_CohnElkies_integral_lowerRiemannLog
import Theorems.Thm_CohnElkies_lowerRiemannLog_zero
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_halfInteger_scaled
import Theorems.Thm_CohnElkies_lowerRiemannLog_continuous
import Theorems.Thm_CohnElkies_lowerRiemannLog_halfInteger_tail_integral_le

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
    (k : ℕ) {ℓ R T : ℝ}
    (hℓeq : ℓ = (k : ℝ) + 1 / 2)
    (hℓone : 1 ≤ ℓ)
    (hR : 0 < R) (hT : T ≠ 0) :
    lowerGammaBoundaryLog ℓ R (ℓ * T) ≤
      ℓ * (Real.log (Real.pi * R ^ 2 / ℓ) +
        1 + lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := by
  have hℓ : 0 < ℓ := by linarith
  have hratio_nonneg : 0 ≤ (k : ℝ) / ℓ := by positivity
  have hratio_le : (k : ℝ) / ℓ ≤ 1 := by
    apply (div_le_one hℓ).2
    rw [hℓeq]
    linarith
  let q : ℝ → ℝ := lowerRiemannLog T
  have hcont := lowerRiemannLog_continuous hT
  have hfirst : IntervalIntegrable q volume
      (0 : ℝ) ((k : ℝ) / ℓ) :=
    hcont.intervalIntegrable _ _
  have hlast : IntervalIntegrable q volume
      ((k : ℝ) / ℓ) 1 :=
    hcont.intervalIntegrable _ _
  have hsplit :
      (∫ x in (0 : ℝ)..((k : ℝ) / ℓ), q x) +
          (∫ x in ((k : ℝ) / ℓ)..1, q x) =
        ∫ x in (0 : ℝ)..1, q x :=
    intervalIntegral.integral_add_adjacent_intervals
      hfirst hlast
  have hmid := lower_halfInteger_midpointRiemann_error
    hT hℓ k
  have hmidupper :
      ℓ * (∫ x in (0 : ℝ)..((k : ℝ) / ℓ), q x) -
          ∑ j ∈ Finset.range k,
            q (((j : ℝ) + 1 / 2) / ℓ) ≤
        q ((k : ℝ) / ℓ) - q 0 := by
    exact le_trans (le_abs_self _) hmid
  have htail :=
    lowerRiemannLog_halfInteger_tail_integral_le
      k hℓeq hT
  have hsumupper :
      -(∑ j ∈ Finset.range k,
        q (((j : ℝ) + 1 / 2) / ℓ)) ≤
        -ℓ * (∫ x in (0 : ℝ)..1, q x) +
          (q ((k : ℝ) / ℓ) - q 0) +
            (1 / 2 : ℝ) * q 1 := by
    nlinarith
  have hqk : q ((k : ℝ) / ℓ) ≤ q 1 := by
    apply lowerRiemannLog_monotoneOn hT
    · exact (show (k : ℝ) / ℓ ∈ Ici (0 : ℝ) from
        hratio_nonneg)
    · exact (show (1 : ℝ) ∈ Ici (0 : ℝ) by norm_num)
    · exact hratio_le
  have harg : 0 < Real.pi * |T| / 2 := by positivity
  have hargℓ : 0 < Real.pi * ℓ * |T| / 2 := by positivity
  have hargorder :
      Real.pi * |T| / 2 ≤ Real.pi * ℓ * |T| / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hℓone)
      (mul_nonneg Real.pi_pos.le (abs_nonneg T))]
  have hcoth := lowerCoth_log_antitoneOn
    harg hargℓ hargorder
  have hphase := integral_lowerRiemannLog hT
  rw [lowerGammaBoundaryLog_halfInteger_scaled
    k hℓeq hR hT,
    ← lowerRiemannLog_zero T]
  unfold lowerRiemannErrorMajorant
  change
    ℓ * Real.log (Real.pi * R ^ 2 / ℓ) -
        ∑ j ∈ Finset.range k,
          q (((j : ℝ) + 1 / 2) / ℓ) +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * ℓ * |T| / 2)) -
        (1 / 2 : ℝ) * q 0 ≤
      ℓ * (Real.log (Real.pi * R ^ 2 / ℓ) +
        1 + lowerEndpointPhase T) +
        (3 * |q 0| + 2 * |q 1| +
          (1 / 2 : ℝ) *
            Real.log (lowerCoth (Real.pi * |T| / 2)))
  change -(∫ x in (0 : ℝ)..1, q x) =
    1 + lowerEndpointPhase T at hphase
  nlinarith [le_abs_self (q 1), neg_le_abs (q 0),
    abs_nonneg (q 0), abs_nonneg (q 1)]
end CohnElkies

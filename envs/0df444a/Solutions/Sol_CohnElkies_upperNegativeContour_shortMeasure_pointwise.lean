-- Prove2me | solution 1 for CohnElkies.upperNegativeContour_shortMeasure_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/8372bc11-3816-465f-9a5f-bf82f093ab1a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaVarianceDensity_pointwise_bounds

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ε ℓ κ η a : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (hκ : 1 ≤ κ)
    (hη : 0 < η) (hκη : κ + η ≤ 3)
    (ha : 0 < a)
    (hmargin : 0 ≤ shortMargin ε a) :
    ℓ * (-shortShellDensity ε a) * Real.cosh (κ * a) ≤
      (1 - 4 * ε) * upperGammaMeasureDensity ℓ η a := by
  have hfactor : 0 ≤ 1 - 4 * ε := by
    apply (mul_nonneg_iff_of_pos_right hη).mp
    exact mul_nonneg (by linarith [hεsmall]) hη.le
  have hmargintop : shortMargin ε a ≤ 1 - 10 * ε := by
    unfold shortMargin
    nlinarith [mul_nonneg hε.le ha.le]
  have hbase :
      (ℓ / 2) * Real.exp (-η * a) / a ^ 2 ≤
        upperGammaMeasureDensity ℓ η a := by
    have hvariance :=
      (upperGammaVarianceDensity_pointwise_bounds
        (η := η) hℓ ha).1
    apply (div_le_iff₀ (sq_pos_of_pos ha)).2
    nlinarith
  have hbasepos :
      0 ≤ (ℓ / 2) * Real.exp (-η * a) / a ^ 2 := by
    positivity
  have hratio :
      Real.cosh (κ * a) / Real.cosh a ≤
        Real.exp ((κ - 1) * a) := by
    convert! cosh_ratio_upper ha.le
      (sub_nonneg.mpr hκ) using 1; ring_nf
  have hexp :
      Real.exp ((η - 2) * a) *
        Real.exp ((κ - 1) * a) ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff]
    nlinarith [mul_nonneg
      (show 0 ≤ 3 - (κ + η) by linarith) ha.le]
  have hcoefficient :
      shortMargin ε a * Real.exp ((η - 2) * a) *
          (Real.cosh (κ * a) / Real.cosh a) ≤
        1 - 4 * ε := by
    calc
      shortMargin ε a * Real.exp ((η - 2) * a) *
          (Real.cosh (κ * a) / Real.cosh a) ≤
        shortMargin ε a * Real.exp ((η - 2) * a) *
          Real.exp ((κ - 1) * a) := by
          gcongr
      _ = shortMargin ε a *
          (Real.exp ((η - 2) * a) *
            Real.exp ((κ - 1) * a)) := by ring
      _ ≤ shortMargin ε a := by
          simpa using! mul_le_mul_of_nonneg_left hexp hmargin
      _ ≤ 1 - 10 * ε := hmargintop
      _ ≤ 1 - 4 * ε := by linarith
  have hidentity :
      ℓ * (-shortShellDensity ε a) * Real.cosh (κ * a) =
        (shortMargin ε a * Real.exp ((η - 2) * a) *
          (Real.cosh (κ * a) / Real.cosh a)) *
          ((ℓ / 2) * Real.exp (-η * a) / a ^ 2) := by
    have he : Real.exp ((η - 2) * a) *
        Real.exp (-η * a) = Real.exp (-2 * a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold shortShellDensity
    field_simp [ha.ne', (Real.cosh_pos a).ne']
    calc
      shortMargin ε a * Real.exp (-(2 * a)) =
          shortMargin ε a *
            (Real.exp ((η - 2) * a) *
              Real.exp (-η * a)) := by
            rw [he]
            congr 1
            ring_nf
      _ = shortMargin ε a * Real.exp (a * (η - 2)) *
            Real.exp (-(a * η)) := by
            rw [show a * (η - 2) = (η - 2) * a by ring,
              show -(a * η) = -η * a by ring]
            ring
  rw [hidentity]
  calc
    (shortMargin ε a * Real.exp ((η - 2) * a) *
        (Real.cosh (κ * a) / Real.cosh a)) *
        ((ℓ / 2) * Real.exp (-η * a) / a ^ 2) ≤
      (1 - 4 * ε) *
        ((ℓ / 2) * Real.exp (-η * a) / a ^ 2) :=
      mul_le_mul_of_nonneg_right hcoefficient hbasepos
    _ ≤ (1 - 4 * ε) * upperGammaMeasureDensity ℓ η a :=
      mul_le_mul_of_nonneg_left hbase hfactor
end CohnElkies

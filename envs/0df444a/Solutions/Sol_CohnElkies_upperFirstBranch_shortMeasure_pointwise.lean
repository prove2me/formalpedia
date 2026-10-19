-- Prove2me | solution 1 for CohnElkies.upperFirstBranch_shortMeasure_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/92ae7d95-4267-4b3e-a4f0-c02bca7057fe

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaVarianceDensity_pointwise_bounds
import Theorems.Thm_CohnElkies_upperFirstBranch_shortRatio_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u a : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (ha : 0 < a)
    (hulower : -1 ≤ u)
    (huupper : u ≤ 1 + ε / 2)
    (hmargin : 0 ≤ shortMargin ε a) :
    ℓ * (-shortShellDensity ε a) * Real.cosh (u * a) ≤
      (1 - 4 * ε) *
        upperGammaMeasureDensity ℓ (1 + u) a := by
  have hfactor : 0 ≤ 1 - 4 * ε := by
    linarith
  have hratio := upperFirstBranch_shortRatio_le
    hε ha.le hulower huupper hmargin
  have hvariance :=
    (upperGammaVarianceDensity_pointwise_bounds
      (η := 1 + u) hℓ ha).1
  have hbase :
      (ℓ / 2) * Real.exp (-(1 + u) * a) /
          a ^ 2 ≤
        upperGammaMeasureDensity ℓ (1 + u) a := by
    apply (div_le_iff₀
      (sq_pos_of_pos ha)).2
    nlinarith
  have hbasepositive :
      0 ≤ (ℓ / 2) *
        Real.exp (-(1 + u) * a) / a ^ 2 := by
    positivity
  have hidentity :
      ℓ * (-shortShellDensity ε a) *
          Real.cosh (u * a) =
        (shortMargin ε a *
          Real.exp ((u - 1) * a) *
            (Real.cosh (u * a) / Real.cosh a)) *
          ((ℓ / 2) * Real.exp (-(1 + u) * a) /
            a ^ 2) := by
    have hexp :
        Real.exp (a * (u - 1)) *
          Real.exp (-(a * (1 + u))) =
            Real.exp (-(2 * a)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold shortShellDensity
    field_simp [ha.ne', (Real.cosh_pos a).ne']
    rw [← hexp]
    ring
  rw [hidentity]
  calc
    (shortMargin ε a *
        Real.exp ((u - 1) * a) *
          (Real.cosh (u * a) / Real.cosh a)) *
        ((ℓ / 2) * Real.exp (-(1 + u) * a) /
          a ^ 2) ≤
      (1 - 4 * ε) *
        ((ℓ / 2) * Real.exp (-(1 + u) * a) /
          a ^ 2) :=
      mul_le_mul_of_nonneg_right hratio hbasepositive
    _ ≤ (1 - 4 * ε) *
          upperGammaMeasureDensity ℓ (1 + u) a :=
      mul_le_mul_of_nonneg_left hbase hfactor
end CohnElkies

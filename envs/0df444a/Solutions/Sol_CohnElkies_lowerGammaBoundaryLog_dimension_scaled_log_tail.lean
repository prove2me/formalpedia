-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_dimension_scaled_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/d61970c7-226b-4e1b-aa56-f053cd079467

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_log_tail

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) {c Y : ℝ}
    (hc : 0 < c) (hY : Y ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2)
      (c * Real.sqrt d) (((d : ℝ) / 2) * Y) ≤
      ((d : ℝ) / 2) *
        Real.log (4 * Real.pi * c ^ 2 / |Y|) +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth
            (Real.pi * |((d : ℝ) / 2) * Y| / 2)) := by
  have hdreal : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hℓ : 0 < (d : ℝ) / 2 := half_pos hdreal
  have hR : 0 < c * Real.sqrt d :=
    mul_pos hc (Real.sqrt_pos.2 hdreal)
  have hy : ((d : ℝ) / 2) * Y ≠ 0 :=
    mul_ne_zero hℓ.ne' hY
  have htail := lowerGammaBoundaryLog_dimension_log_tail
    hd hR hy
  have hratio :
      2 * Real.pi * (c * Real.sqrt d) ^ 2 /
        |((d : ℝ) / 2) * Y| =
          4 * Real.pi * c ^ 2 / |Y| := by
    rw [abs_mul, abs_of_pos hℓ, mul_pow,
      Real.sq_sqrt hdreal.le]
    field_simp [hℓ.ne', abs_ne_zero.mpr hY, hdreal.ne']
    ring
  rw [hratio] at htail
  exact htail
end CohnElkies

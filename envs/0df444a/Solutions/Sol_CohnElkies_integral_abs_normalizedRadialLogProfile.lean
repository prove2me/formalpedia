-- Prove2me | solution 1 for CohnElkies.integral_abs_normalizedRadialLogProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/77013fb8-ffa6-4ad2-97ba-991060be5a7a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialL1Mass_pos
import Theorems.Thm_CohnElkies_integral_scaled_exp_change_Ioi
import Theorems.Thm_CohnElkies_radialL1Mass_eq
import Theorems.Thm_CohnElkies_abs_normalizedRadialLogProfile

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal
namespace CohnElkies
theorem _root_.solution {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (hradial : IsRadial g)
    (hreal : IsRealValued g) (hnonzero : g ≠ 0)
    {R : ℝ} (hR : 0 < R) :
    (∫ v : ℝ, |normalizedRadialLogProfile hd g R v|) = 1 := by
  have hmass : 0 < radialL1Mass g := radialL1Mass_pos g hnonzero
  calc
    (∫ v : ℝ, |normalizedRadialLogProfile hd g R v|) =
        ∫ v : ℝ,
          (radialSurfaceArea d / radialL1Mass g) *
            ((R * Real.exp v) *
              ((R * Real.exp v) ^ (d - 1) *
                ‖radialProfile hd g (R * Real.exp v)‖)) := by
      apply integral_congr_ae
      filter_upwards [] with v
      exact abs_normalizedRadialLogProfile hd g hreal hnonzero hR v
    _ = (radialSurfaceArea d / radialL1Mass g) *
          ∫ v : ℝ,
            (R * Real.exp v) *
              ((R * Real.exp v) ^ (d - 1) *
                ‖radialProfile hd g (R * Real.exp v)‖) := by
      rw [integral_const_mul]
    _ = (radialSurfaceArea d / radialL1Mass g) *
          ∫ r : ℝ in Ioi 0,
            r ^ (d - 1) * ‖radialProfile hd g r‖ := by
      rw [integral_scaled_exp_change_Ioi hR
        (fun r : ℝ => r ^ (d - 1) * ‖radialProfile hd g r‖)]
      simp [smul_eq_mul]
    _ = (radialSurfaceArea d *
          ∫ r : ℝ in Ioi 0,
            r ^ (d - 1) * ‖radialProfile hd g r‖) /
            radialL1Mass g := by
      ring
    _ = 1 := by
      rw [← radialL1Mass_eq hd g hradial]
      exact div_self hmass.ne'
end CohnElkies

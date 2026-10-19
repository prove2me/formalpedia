-- Prove2me | solution 1 for CohnElkies.integral_normalizedRadialLogProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/c5257d1b-93a5-4f73-86d7-4f95aa268b5a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integral_scaled_exp_change_Ioi
import Theorems.Thm_CohnElkies_integral_radialProfile_re
import Theorems.Thm_CohnElkies_normalizedRadialLogProfile_eq

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
    (g : TestFunction d) (hg : IsRadial g)
    {R : ℝ} (hR : 0 < R) :
    (∫ v : ℝ, normalizedRadialLogProfile hd g R v) =
      (∫ x : Euclidean d, (g x).re) / radialL1Mass g := by
  calc
    (∫ v : ℝ, normalizedRadialLogProfile hd g R v) =
        ∫ v : ℝ,
          (radialSurfaceArea d / radialL1Mass g) *
            ((R * Real.exp v) *
              ((R * Real.exp v) ^ (d - 1) *
                (radialProfile hd g (R * Real.exp v)).re)) := by
      apply integral_congr_ae
      filter_upwards [] with v
      exact normalizedRadialLogProfile_eq hd g R v
    _ = (radialSurfaceArea d / radialL1Mass g) *
          ∫ v : ℝ,
            (R * Real.exp v) *
              ((R * Real.exp v) ^ (d - 1) *
                (radialProfile hd g (R * Real.exp v)).re) := by
      rw [integral_const_mul]
    _ = (radialSurfaceArea d / radialL1Mass g) *
          ∫ r : ℝ in Ioi 0,
            r ^ (d - 1) * (radialProfile hd g r).re := by
      rw [integral_scaled_exp_change_Ioi hR
        (fun r : ℝ => r ^ (d - 1) *
          (radialProfile hd g r).re)]
      simp [smul_eq_mul]
    _ = (∫ x : Euclidean d, (g x).re) / radialL1Mass g := by
      rw [integral_radialProfile_re hd g hg]
      ring
end CohnElkies

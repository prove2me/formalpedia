-- Prove2me | solution 1 for CohnElkies.abs_normalizedRadialLogProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/7d830bc3-6526-4878-9a8f-a2bb14096dc7

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialL1Mass_pos
import Theorems.Thm_CohnElkies_norm_radialProfile_eq_abs_re
import Theorems.Thm_CohnElkies_radialLogRadius_pow

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
    (g : TestFunction d) (hreal : IsRealValued g)
    (hnonzero : g ≠ 0) {R : ℝ} (hR : 0 < R) (v : ℝ) :
    |normalizedRadialLogProfile hd g R v| =
      (radialSurfaceArea d / radialL1Mass g) *
        ((R * Real.exp v) *
          ((R * Real.exp v) ^ (d - 1) *
            ‖radialProfile hd g (R * Real.exp v)‖)) := by
  have hcoefficient : 0 < radialSurfaceArea d / radialL1Mass g :=
    div_pos (radialSurfaceArea_pos hd) (radialL1Mass_pos g hnonzero)
  have hradius : 0 < R * Real.exp v :=
    mul_pos hR (Real.exp_pos v)
  calc
    |normalizedRadialLogProfile hd g R v| =
        |radialSurfaceArea d / radialL1Mass g| *
          |(R * Real.exp v) ^ d| *
            |(radialProfile hd g (R * Real.exp v)).re| := by
      simp [normalizedRadialLogProfile, abs_mul, mul_assoc]
    _ = (radialSurfaceArea d / radialL1Mass g) *
          ((R * Real.exp v) *
            ((R * Real.exp v) ^ (d - 1) *
              ‖radialProfile hd g (R * Real.exp v)‖)) := by
      rw [abs_of_pos hcoefficient, abs_pow, abs_of_pos hradius,
        ← norm_radialProfile_eq_abs_re hd g hreal,
        radialLogRadius_pow hd]
      ring
end CohnElkies

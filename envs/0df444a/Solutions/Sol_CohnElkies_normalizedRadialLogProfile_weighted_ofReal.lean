-- Prove2me | solution 1 for CohnElkies.normalizedRadialLogProfile_weighted_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/42b46b04-8e5e-4cc8-a03d-84c368f6fc60

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedRadialLogProfile_ofReal

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hreal : IsRealValued f)
    (R a v : ℝ) :
    (Real.exp (-a * v) : ℂ) *
        (normalizedRadialLogProfile hd f R v : ℂ) =
      ((radialSurfaceArea d / radialL1Mass f * R ^ d : ℝ) : ℂ) *
        (Real.exp (((d : ℝ) - a) * v) : ℂ) *
        radialProfile hd f (R * Real.exp v) := by
  have hexp :
      Real.exp (-a * v) * (R * Real.exp v) ^ d =
        R ^ d * Real.exp (((d : ℝ) - a) * v) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    calc
      Real.exp (-a * v) *
          (R ^ d * Real.exp ((d : ℝ) * v)) =
        R ^ d *
          (Real.exp (-a * v) * Real.exp ((d : ℝ) * v)) := by
        ring
      _ = R ^ d * Real.exp (-a * v + (d : ℝ) * v) := by
        rw [← Real.exp_add]
      _ = R ^ d * Real.exp (((d : ℝ) - a) * v) := by
        congr 1
        ring_nf
  rw [normalizedRadialLogProfile_ofReal hd f hreal R v]
  have hcomplex := congrArg (fun x : ℝ => (x : ℂ)) hexp
  push_cast at hcomplex ⊢
  linear_combination
    (((radialSurfaceArea d : ℝ) : ℂ) /
      ((radialL1Mass f : ℝ) : ℂ) *
      radialProfile hd f (R * Real.exp v)) * hcomplex
end CohnElkies

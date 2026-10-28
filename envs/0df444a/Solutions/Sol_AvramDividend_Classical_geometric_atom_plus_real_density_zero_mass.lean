-- Prove2me | solution 1 for AvramDividend.Classical.geometric_atom_plus_real_density_zero_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:30:48.656894+00:00
-- url     : https://prove2.me/submissions/ef5c8ff6-8944-4697-beb8-a1b308890105

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- A geometrically weighted Dirac atom remains exactly the initial coefficient. -/
theorem solution (r : ℝ) (_hr : 0 ≤ r) (f : ℝ → ℝ)
    (β : Measure ℝ)
    (hβ : β = ENNReal.ofReal r • (Measure.dirac (0 : ℝ) +
      (volume : Measure ℝ).withDensity (fun x : ℝ => ENNReal.ofReal (f x)))) :
    β ({(0 : ℝ)} : Set ℝ) = ENNReal.ofReal r := by
  have hzero :
      ((volume : Measure ℝ).withDensity
        (fun x : ℝ => ENNReal.ofReal (f x))) ({(0 : ℝ)} : Set ℝ) = 0 :=
    (withDensity_absolutelyContinuous _ _) (by simp)
  rw [hβ, Measure.smul_apply, Measure.add_apply]
  simp [hzero]
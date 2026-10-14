-- Prove2me | solution 1 for DistCov.Converse.Ddiff_dirac_neg
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T23:59:58.914988+00:00
-- url     : https://prove2.me/submissions/e819406e-b088-4595-9b9c-0b0e4dc77b58

import Mathlib
import Definitions.Def_DistCov_Converse_Setting

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace DistCovConverseDirac

theorem energy_dirac
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (x y : X) :
    DistCov.Indep.energy (Measure.dirac x) (Measure.dirac y) = dist x y := by
  simp [DistCov.Indep.energy, Measure.dirac_prod_dirac]

theorem Ddiff_dirac_eq
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (x y : X) :
    DistCov.Indep.Ddiff (Measure.dirac x) (Measure.dirac y) = -2 * dist x y := by
  simp [DistCov.Indep.Ddiff, energy_dirac]

end DistCovConverseDirac

theorem solution
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (x₁ x₂ : X) (hx : x₁ ≠ x₂) :
    DistCov.Indep.Ddiff (Measure.dirac x₁) (Measure.dirac x₂) < 0 := by
  rw [DistCovConverseDirac.Ddiff_dirac_eq]
  have hdist : 0 < dist x₁ x₂ := dist_pos.mpr hx
  linarith

#print axioms solution

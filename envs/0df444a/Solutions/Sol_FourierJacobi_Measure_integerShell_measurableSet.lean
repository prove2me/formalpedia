-- Prove2me | solution 1 for FourierJacobi.Measure.integerShell_measurableSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:52.712245+00:00
-- url     : https://prove2.me/submissions/afce2223-1300-43b1-99c6-342563e6ba39

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Measure_integerShell_eq_sdiff
import Theorems.Thm_FourierJacobi_Measure_integerBall_measurableSet

set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise WithZero
open FourierJacobi FourierJacobi.Measure
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.integerShells_t2Space
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Measure.integerShells_additiveHaar_regular
namespace FourierJacobi.Measure
theorem _root_.solution (n : ℤ) : MeasurableSet (integerShell K n) := by
  rw [integerShell_eq_sdiff]
  exact (integerBall_measurableSet K n).diff (integerBall_measurableSet K (n + 1))
end FourierJacobi.Measure

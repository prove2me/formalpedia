-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_real_integerBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:27.867277+00:00
-- url     : https://prove2.me/submissions/b6e9497a-fdee-4b59-8c65-dd054f2b12a1

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_integerBall
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



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
theorem _root_.solution (n : ℤ) :
    (additiveHaar K).real (integerBall K n) = (residueCardinality K : ℝ) ^ (-n) := by
  simp [measureReal_def, additiveHaar_integerBall, zpow_neg]
end FourierJacobi.Measure

-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_integerShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:18.618256+00:00
-- url     : https://prove2.me/submissions/bc4560b5-71eb-49b7-8b09-38d77150b5aa

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_integerShell
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_integerShell_ne_top

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
    additiveHaar K (integerShell K n) =
      ENNReal.ofReal ((1 - (residueCardinality K : ℝ)⁻¹) *
        (residueCardinality K : ℝ) ^ (-n)) := by
  calc
    _ = ENNReal.ofReal ((additiveHaar K).real (integerShell K n)) :=
      (ENNReal.ofReal_toReal (additiveHaar_integerShell_ne_top K n)).symm
    _ = _ := congrArg ENNReal.ofReal (additiveHaar_real_integerShell K n)
end FourierJacobi.Measure

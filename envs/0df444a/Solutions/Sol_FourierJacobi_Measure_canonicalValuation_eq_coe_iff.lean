-- Prove2me | solution 1 for FourierJacobi.Measure.canonicalValuation_eq_coe_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:33.007863+00:00
-- url     : https://prove2.me/submissions/37556e47-a8f2-4707-8c2c-a9933f241dfe

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Measure_extendedNegLog_eq_coe_iff

set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise WithZero
open FourierJacobi FourierJacobi.Measure
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.integerShells_t2Space
namespace FourierJacobi.Measure
theorem _root_.solution (x : K) (n : ℤ) :
    localFieldValuation K x = (n : WithTop ℤ) ↔
      discreteValuation K x = WithZero.exp (-n) :=
  extendedNegLog_eq_coe_iff (discreteValuation K x) n
end FourierJacobi.Measure

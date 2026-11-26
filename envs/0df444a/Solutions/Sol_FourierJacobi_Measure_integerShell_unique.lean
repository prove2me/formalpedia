-- Prove2me | solution 1 for FourierJacobi.Measure.integerShell_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:29.854854+00:00
-- url     : https://prove2.me/submissions/74b4b6fc-915f-4360-acdc-b390ab7fd225

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells

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
theorem _root_.solution (x : K) (m n : ℤ)
    (hm : x ∈ integerShell K m) (hn : x ∈ integerShell K n) : m = n :=
  WithTop.coe_injective (hm.symm.trans hn)
end FourierJacobi.Measure

-- Prove2me | solution 1 for FourierJacobi.Measure.unitValuationShell_measurableSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:41.351816+00:00
-- url     : https://prove2.me/submissions/6c5ebd78-133f-4cd1-9def-cbe4be8da2cc

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.Topology.Algebra.Group.Units
import Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
import Theorems.Thm_FourierJacobi_Measure_unitValuationShell_isOpen

set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal Pointwise
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.multiplicativeHaar_t2Space
variable [MeasurableSpace Kˣ] [BorelSpace Kˣ]
namespace FourierJacobi.Measure
theorem _root_.solution (n : ℤ) : MeasurableSet (unitValuationShell K n) :=
  (unitValuationShell_isOpen K n).measurableSet
end FourierJacobi.Measure

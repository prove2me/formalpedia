-- Prove2me | solution 1 for FourierJacobi.Measure.multiplicativeHaar_real_unitValuationShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:46.156467+00:00
-- url     : https://prove2.me/submissions/aeda1631-f58e-41db-bd7d-69e26796868a

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.Topology.Algebra.Group.Units
import Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



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
theorem _root_.solution (n : ℤ) :
    (multiplicativeHaar K).real (unitValuationShell K n) = 1 := by
  simp only [Measure.real, multiplicativeHaar_unitValuationShell, ENNReal.toReal_one]
end FourierJacobi.Measure

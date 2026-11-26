-- Prove2me | solution 1 for FourierJacobi.Measure.canonicalValuation_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:35.060071+00:00
-- url     : https://prove2.me/submissions/d11c546f-5993-44d6-b4ee-e8dad1e0a633

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Measure_integerShell_measurableSet
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_ne_top
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
theorem _root_.solution [MeasurableSpace (WithTop ℤ)] :
    Measurable (localFieldValuation K) := by
  apply measurable_to_countable'
  intro v
  induction v using WithTop.recTopCoe with
  | top =>
    have heq : (localFieldValuation K) ⁻¹' {⊤} = {0} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact not_iff_not.mp (localFieldValuation_ne_top K x)
    rw [heq]
    exact measurableSet_singleton 0
  | coe n =>
    exact integerShell_measurableSet K n
end FourierJacobi.Measure

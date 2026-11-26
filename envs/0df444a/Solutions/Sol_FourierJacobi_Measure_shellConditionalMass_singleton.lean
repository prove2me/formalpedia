-- Prove2me | solution 1 for FourierJacobi.Measure.shellConditionalMass_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:00.474804+00:00
-- url     : https://prove2.me/submissions/54043a0a-9dc9-4e00-95e1-2340d6537f28

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.shellCollision_t2Space
variable [MeasurableSpace K] [BorelSpace K]
namespace FourierJacobi.Measure
theorem _root_.solution (a : K) (n : ℤ) :
    shellConditionalMass K n {a} = 0 := by
  have h : additiveHaar K ({a} ∩ integerShell K n) = 0 :=
    measure_mono_null Set.inter_subset_left (measure_singleton a)
  simp only [shellConditionalMass, Measure.real, h, ENNReal.toReal_zero, zero_div]
end FourierJacobi.Measure

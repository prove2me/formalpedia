-- Prove2me | solution 1 for FourierJacobi.Measure.distribHaarChar_valuationRingUnits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:25.625816+00:00
-- url     : https://prove2.me/submissions/fced458c-8a14-406e-bfcc-2f6e287d54c8

import Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
import Definitions.Def_FourierJacobi_Measure_UnitScaling
import Theorems.Thm_FourierJacobi_Measure_valuationRingUnits_smul_integers

set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.unitScaling_t2Space
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Measure.unitScaling_additiveHaar_regular
namespace FourierJacobi.Measure
theorem _root_.solution (u : Kˣ) (hu : u ∈ valuationRingUnits K) :
    distribHaarChar K u = 1 := by
  have h := distribHaarChar_mul (additiveHaar K) u (𝒪[K] : Set K)
  rw [valuationRingUnits_smul_integers K u hu, additiveHaar_integers, mul_one] at h
  exact ENNReal.coe_injective h
end FourierJacobi.Measure

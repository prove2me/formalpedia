-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_smul_valuationRingUnits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:22.449939+00:00
-- url     : https://prove2.me/submissions/93dc27ed-9ef5-4a32-a1be-02ea1723a827

import Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
import Definitions.Def_FourierJacobi_Measure_UnitScaling
import Theorems.Thm_FourierJacobi_Measure_distribHaarChar_valuationRingUnits
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



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
theorem _root_.solution (u : Kˣ)
    (hu : u ∈ valuationRingUnits K) (s : Set K) :
    additiveHaar K (u • s) = additiveHaar K s := by
  rw [← distribHaarChar_mul, distribHaarChar_valuationRingUnits K u hu]
  simp only [ENNReal.coe_one, one_mul]
end FourierJacobi.Measure

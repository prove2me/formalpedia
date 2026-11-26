-- Prove2me | solution 1 for FourierJacobi.Measure.paperMultiplicativeHaar_valuationRingUnits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:49.911827+00:00
-- url     : https://prove2.me/submissions/a1aef7a6-14da-4554-8f2c-1df40a43ab54

import Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
import Definitions.Def_FourierJacobi_Measure_PaperMultiplicativeHaar
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel
open scoped ENNReal
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [MeasurableSpace Kˣ] [BorelSpace Kˣ]
namespace FourierJacobi.Measure
theorem _root_.solution :
    paperMultiplicativeHaar K (valuationRingUnits K : Set Kˣ) =
      ENNReal.ofReal (1 - (residueCardinality K : ℝ)⁻¹) := by
  simp only [paperMultiplicativeHaar, Measure.smul_apply,
    multiplicativeHaar_valuationRingUnits, smul_eq_mul, mul_one]
end FourierJacobi.Measure

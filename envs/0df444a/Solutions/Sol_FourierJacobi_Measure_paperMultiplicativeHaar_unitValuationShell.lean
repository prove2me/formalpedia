-- Prove2me | solution 1 for FourierJacobi.Measure.paperMultiplicativeHaar_unitValuationShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:31.660332+00:00
-- url     : https://prove2.me/submissions/be75e119-b5cc-49e5-93ac-0f4f1d77b5e9

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
theorem _root_.solution (n : ℤ) :
    paperMultiplicativeHaar K (unitValuationShell K n) =
      ENNReal.ofReal (1 - (residueCardinality K : ℝ)⁻¹) := by
  simp only [paperMultiplicativeHaar, Measure.smul_apply,
    multiplicativeHaar_unitValuationShell, smul_eq_mul, mul_one]
end FourierJacobi.Measure

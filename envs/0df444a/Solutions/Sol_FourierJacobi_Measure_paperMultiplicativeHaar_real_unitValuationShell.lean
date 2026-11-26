-- Prove2me | solution 1 for FourierJacobi.Measure.paperMultiplicativeHaar_real_unitValuationShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:55.385296+00:00
-- url     : https://prove2.me/submissions/34c0702e-f539-4874-aead-7b1f2973a407

import Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
import Definitions.Def_FourierJacobi_Measure_PaperMultiplicativeHaar
import Theorems.Thm_FourierJacobi_Measure_paperMultiplicativeHaar_unitValuationShell

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
    (paperMultiplicativeHaar K).real (unitValuationShell K n) =
      1 - (residueCardinality K : ℝ)⁻¹ := by
  rw [Measure.real, paperMultiplicativeHaar_unitValuationShell,
    ENNReal.toReal_ofReal (paperMultiplicativeFactor_pos K).le]
end FourierJacobi.Measure

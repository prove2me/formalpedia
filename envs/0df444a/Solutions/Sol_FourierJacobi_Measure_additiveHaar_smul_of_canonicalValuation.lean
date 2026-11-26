-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_smul_of_canonicalValuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:25.735069+00:00
-- url     : https://prove2.me/submissions/48b250ca-0ee1-4df7-bdc1-24cd76b5d082

import Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
import Definitions.Def_FourierJacobi_Measure_UnitScaling
import Theorems.Thm_FourierJacobi_Measure_distribHaarChar_eq_of_canonicalValuation

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
theorem _root_.solution (u : Kˣ) (n : ℤ)
    (hu : localFieldValuation K (u : K) = (n : WithTop ℤ)) (s : Set K) :
    additiveHaar K (u • s) =
      (↑(((residueCardinality K : ℝ≥0)⁻¹) ^ n) : ℝ≥0∞) * additiveHaar K s := by
  rw [← distribHaarChar_mul, distribHaarChar_eq_of_canonicalValuation K u n hu]
end FourierJacobi.Measure

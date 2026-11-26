-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_real_smul_of_canonicalValuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:11.991798+00:00
-- url     : https://prove2.me/submissions/bb7f3f2a-fe2e-4518-90e4-2dbfaa05fb6c

import Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
import Definitions.Def_FourierJacobi_Measure_UnitScaling
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_smul_of_canonicalValuation
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
theorem _root_.solution (u : Kˣ) (n : ℤ)
    (hu : localFieldValuation K (u : K) = (n : WithTop ℤ)) (s : Set K) :
    (additiveHaar K).real (u • s) =
      (residueCardinality K : ℝ) ^ (-n) * (additiveHaar K).real s := by
  rw [Measure.real, additiveHaar_smul_of_canonicalValuation K u n hu,
    ENNReal.toReal_mul, ENNReal.coe_toReal]
  simp only [NNReal.coe_zpow, NNReal.coe_inv, NNReal.coe_natCast, inv_zpow, zpow_neg]
  rfl
end FourierJacobi.Measure

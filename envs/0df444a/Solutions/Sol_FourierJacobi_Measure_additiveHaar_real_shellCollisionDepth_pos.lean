-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_real_shellCollisionDepth_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:13.193996+00:00
-- url     : https://prove2.me/submissions/8d8feed7-6675-42fa-863f-773969b1e18b

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Theorems.Thm_FourierJacobi_Measure_shellCollisionDepth_eq_preimage
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_integerShell
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
theorem _root_.solution (a : K) (n : ℤ) (c : ℕ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) (hc : 0 < c) :
    (additiveHaar K).real (shellCollisionDepth K a n c) =
      (1 - (residueCardinality K : ℝ)⁻¹) *
        (residueCardinality K : ℝ) ^ (-(n + (c : ℤ))) := by
  rw [shellCollisionDepth_eq_preimage K a n c ha hc]
  simpa only [Measure.real, sub_eq_add_neg, measure_preimage_add_right] using
    additiveHaar_real_integerShell K (n + c)
end FourierJacobi.Measure

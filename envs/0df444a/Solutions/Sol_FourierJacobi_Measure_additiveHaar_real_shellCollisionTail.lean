-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_real_shellCollisionTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:04.472645+00:00
-- url     : https://prove2.me/submissions/ea45721e-3874-47d2-ad21-b7a1cfbb0ad6

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Theorems.Thm_FourierJacobi_Measure_shellCollisionTail_eq_preimage
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_integerBall
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
    (additiveHaar K).real (shellCollisionTail K a n c) =
      (residueCardinality K : ℝ) ^ (-(n + (c : ℤ))) := by
  rw [shellCollisionTail_eq_preimage K a n c ha hc]
  simpa only [Measure.real, sub_eq_add_neg, measure_preimage_add_right] using
    additiveHaar_real_integerBall K (n + c)
end FourierJacobi.Measure

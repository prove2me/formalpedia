-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_real_prod_jointCollisionDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:08.73607+00:00
-- url     : https://prove2.me/submissions/f412021e-abde-49c9-82e3-7d697c724801

import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Theorems.Thm_FourierJacobi_Measure_shellCollisionProbability_nonneg
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_prod_jointCollisionDepth
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_integerShell


set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.jointCollision_t2Space
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Measure.jointCollision_secondCountable
attribute [local instance] FourierJacobi.Measure.jointCollision_additiveHaar_sigmaFinite
namespace FourierJacobi.Measure
theorem _root_.solution (z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) (hlocus : 2 * h = j + s) :
    ((additiveHaar K).prod (additiveHaar K)).real (jointCollisionDepth K z j h s c) =
      shellCollisionProbability K c *
        ((1 - (residueCardinality K : ℝ)⁻¹) ^ 2 *
          ((residueCardinality K : ℝ) ^ (-j) * (residueCardinality K : ℝ) ^ (-h))) := by
  rw [Measure.real, additiveHaar_prod_jointCollisionDepth K z j h s c hz hlocus,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (mul_nonneg (shellCollisionProbability_nonneg K c) measureReal_nonneg)]
  change shellCollisionProbability K c * (additiveHaar K).real (integerShell K j) *
    (additiveHaar K).real (integerShell K h) = _
  rw [additiveHaar_real_integerShell, additiveHaar_real_integerShell]
  ring
end FourierJacobi.Measure

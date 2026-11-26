-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_prod_sourceJointCollisionDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:45.896121+00:00
-- url     : https://prove2.me/submissions/5d4c396c-7405-470a-907e-df05309c41b1

import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Theorems.Thm_FourierJacobi_Measure_sourceJointCollisionDepth_eq_swap
import Theorems.Thm_FourierJacobi_Measure_jointCollisionDepth_measurableSet
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_prod_jointCollisionDepth

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
    ((additiveHaar K).prod (additiveHaar K)) (sourceJointCollisionDepth K z j h c) =
      ENNReal.ofReal (shellCollisionProbability K c *
        (additiveHaar K).real (integerShell K j)) * additiveHaar K (integerShell K h) := by
  rw [sourceJointCollisionDepth_eq_swap K z j h s c hz,
    ← Measure.map_apply measurable_swap (jointCollisionDepth_measurableSet K z j h s c),
    Measure.prod_swap]
  exact additiveHaar_prod_jointCollisionDepth K z j h s c hz hlocus
end FourierJacobi.Measure

-- Prove2me | solution 1 for FourierJacobi.Measure.sourceJointCollisionDepth_measurableSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:27.6208+00:00
-- url     : https://prove2.me/submissions/d2b51d8f-5f4e-4ece-ad18-78770b957512

import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Theorems.Thm_FourierJacobi_Measure_sourceJointCollisionDepth_eq_swap
import Theorems.Thm_FourierJacobi_Measure_jointCollisionDepth_measurableSet

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
    (hz : localFieldValuation K z = (s : WithTop ℤ)) :
    MeasurableSet (sourceJointCollisionDepth K z j h c) := by
  rw [sourceJointCollisionDepth_eq_swap K z j h s c hz]
  exact (jointCollisionDepth_measurableSet K z j h s c).preimage measurable_swap
end FourierJacobi.Measure

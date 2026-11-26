-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_shellCollisionDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:47:20.507733+00:00
-- url     : https://prove2.me/submissions/cd70c1d8-b9fd-447d-8ec2-9507f5d45443

import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_shellCollisionDepth
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_integerShell_ne_top
import Theorems.Thm_FourierJacobi_Measure_shellCollisionDepth_subset


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
theorem _root_.solution (a : K) (n : ℤ) (c : ℕ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) :
    additiveHaar K (shellCollisionDepth K a n c) =
      ENNReal.ofReal (shellCollisionProbability K c *
        (additiveHaar K).real (integerShell K n)) := by
  rw [← additiveHaar_real_shellCollisionDepth K a n c ha]
  exact (ENNReal.ofReal_toReal (measure_ne_top_of_subset
    (shellCollisionDepth_subset K a n c) (additiveHaar_integerShell_ne_top K n))).symm
end FourierJacobi.Measure

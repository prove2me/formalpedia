-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_real_shellCollisionDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:22.014086+00:00
-- url     : https://prove2.me/submissions/e9290313-347d-49cb-b110-09c1b438f90a

import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Theorems.Thm_FourierJacobi_Measure_shellConditionalMass_collisionDepth
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_integerShell_pos
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
    (additiveHaar K).real (shellCollisionDepth K a n c) =
      shellCollisionProbability K c * (additiveHaar K).real (integerShell K n) := by
  have he := shellConditionalMass_collisionDepth K a n c ha
  rw [shellConditionalMass,
    Set.inter_eq_self_of_subset_left (shellCollisionDepth_subset K a n c)] at he
  exact (div_eq_iff (additiveHaar_real_integerShell_pos K n).ne').mp he
end FourierJacobi.Measure

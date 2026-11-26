-- Prove2me | solution 1 for FourierJacobi.Measure.shellConditionalMass_collisionDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:20.138844+00:00
-- url     : https://prove2.me/submissions/83be65bc-8975-4a86-9fec-5d7883acb222

import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Theorems.Thm_FourierJacobi_Measure_shellConditionalMass_collisionDepth_pos
import Theorems.Thm_FourierJacobi_Measure_shellConditionalMass_collisionDepth_zero
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.actualEntryInteger_coe
attribute [local simp] FourierJacobi.Valuations.actualMinorInteger_coe
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



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
    shellConditionalMass K n (shellCollisionDepth K a n c) = shellCollisionProbability K c := by
  by_cases hc : c = 0
  · subst c
    exact shellConditionalMass_collisionDepth_zero K a n ha
  · simpa only [shellCollisionProbability, if_neg hc] using
      shellConditionalMass_collisionDepth_pos K a n c ha (Nat.pos_of_ne_zero hc)
end FourierJacobi.Measure

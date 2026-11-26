-- Prove2me | solution 1 for FourierJacobi.Measure.sourceJointCollisionDepth_eq_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:48.950842+00:00
-- url     : https://prove2.me/submissions/fbe39eb8-a496-423a-bf6b-4f93af8076dd

import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Theorems.Thm_FourierJacobi_Measure_collision_ratio_valuation_iff
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
namespace FourierJacobi.Measure
theorem _root_.solution (z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) :
    sourceJointCollisionDepth K z j h c =
      Prod.swap ⁻¹' jointCollisionDepth K z j h s c := by
  ext p
  simp only [sourceJointCollisionDepth, jointCollisionDepth, Set.mem_preimage,
    Set.mem_ofPred_eq, Prod.swap]
  by_cases hx : localFieldValuation K p.1 = (j : WithTop ℤ)
  · rw [collision_ratio_valuation_iff K p.1 p.2 z j s c hx hz]
    tauto
  · tauto
end FourierJacobi.Measure

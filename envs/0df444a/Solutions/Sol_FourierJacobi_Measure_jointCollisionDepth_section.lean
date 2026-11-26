-- Prove2me | solution 1 for FourierJacobi.Measure.jointCollisionDepth_section
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:26.856796+00:00
-- url     : https://prove2.me/submissions/904415de-b663-48b3-b45f-18aed95c68cd

import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Theorems.Thm_FourierJacobi_Measure_shellCollisionDepth_mem_iff
import Theorems.Thm_FourierJacobi_Measure_coe_add_eq_coe_add_iff
import Theorems.Thm_FourierJacobi_Measure_determinant_valuation_at_center
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
theorem _root_.solution (y z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) :
    Prod.mk y ⁻¹' jointCollisionDepth K z j h s c =
      if localFieldValuation K y = (h : WithTop ℤ)
      then shellCollisionDepth K (y ^ 2 / z) j c else ∅ := by
  split_ifs with hy
  · ext x
    simp only [jointCollisionDepth, Set.mem_preimage, Set.mem_ofPred_eq, hy, true_and,
      shellCollisionDepth_mem_iff, determinant_valuation_at_center K x y z s hz]
    rw [show j + s + (c : ℤ) = s + (j + c) by omega, coe_add_eq_coe_add_iff]
  · ext x
    simp only [jointCollisionDepth, Set.mem_preimage, Set.mem_ofPred_eq, hy,
      false_and, Set.mem_empty_iff_false]
end FourierJacobi.Measure

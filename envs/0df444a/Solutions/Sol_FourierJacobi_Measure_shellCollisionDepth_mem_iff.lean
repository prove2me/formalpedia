-- Prove2me | solution 1 for FourierJacobi.Measure.shellCollisionDepth_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:44:18.915959+00:00
-- url     : https://prove2.me/submissions/cf9babbd-470e-4ffa-b624-f98612aa8607

import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Measure_JointCollision
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
theorem _root_.solution (a x : K) (n : ℤ) (c : ℕ) :
    x ∈ shellCollisionDepth K a n c ↔
      localFieldValuation K x = (n : WithTop ℤ) ∧
        localFieldValuation K (x - a) = ((n + (c : ℤ) : ℤ) : WithTop ℤ) := by
  simp only [shellCollisionDepth, shellCollisionTail, integerShell, integerBall,
    Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  by_cases hx : localFieldValuation K x = (n : WithTop ℤ)
  · simp only [hx, true_and]
    generalize localFieldValuation K (x - a) = v
    induction v using WithTop.recTopCoe with
    | top => simp only [le_top, not_true_eq_false, and_false, WithTop.top_ne_coe]
    | coe m =>
      simp only [WithTop.coe_inj, WithTop.coe_le_coe]
      omega
  · simp only [hx, false_and, not_false_eq_true, and_true]
end FourierJacobi.Measure

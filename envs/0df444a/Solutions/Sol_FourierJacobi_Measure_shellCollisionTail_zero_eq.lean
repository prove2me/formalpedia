-- Prove2me | solution 1 for FourierJacobi.Measure.shellCollisionTail_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:01.573814+00:00
-- url     : https://prove2.me/submissions/0145ab51-fd38-410e-8f52-546338663813

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.shellCollision_t2Space
namespace FourierJacobi.Measure
theorem _root_.solution (a : K) (n : ℤ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) :
    shellCollisionTail K a n 0 = integerShell K n := by
  apply Set.inter_eq_self_of_subset_left
  intro x hx
  change (n + (0 : ℕ) : ℤ) ≤ localFieldValuation K (x - a)
  simp only [Nat.cast_zero, add_zero]
  exact (localFieldValuation K).map_le_sub (le_of_eq hx.symm) (le_of_eq ha.symm)
end FourierJacobi.Measure

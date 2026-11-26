-- Prove2me | solution 1 for FourierJacobi.Measure.determinant_valuation_at_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:44:35.017398+00:00
-- url     : https://prove2.me/submissions/eecab42b-0b49-4408-b92c-fbec81233677

import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_ne_top
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
theorem _root_.solution (x y z : K) (s : ℤ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) :
    localFieldValuation K (y ^ 2 - x * z) =
      (s : WithTop ℤ) + localFieldValuation K (x - y ^ 2 / z) := by
  have hz0 : z ≠ 0 := (localFieldValuation_ne_top K z).mp (by rw [hz]; simp)
  have he : y ^ 2 - x * z = (-z) * (x - y ^ 2 / z) := by
    field_simp
    ring
  rw [he, (localFieldValuation K).map_mul, (localFieldValuation K).map_neg, hz]
end FourierJacobi.Measure

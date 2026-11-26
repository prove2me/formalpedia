-- Prove2me | solution 1 for FourierJacobi.Measure.coe_add_eq_coe_add_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:44:31.752121+00:00
-- url     : https://prove2.me/submissions/7eda6390-5fc0-490b-98be-8aedc265af3b

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
theorem _root_.solution (s n : ℤ) (v : WithTop ℤ) :
    (s : WithTop ℤ) + v = ((s + n : ℤ) : WithTop ℤ) ↔ v = (n : WithTop ℤ) := by
  induction v using WithTop.recTopCoe with
  | top => simp only [WithTop.add_top, WithTop.top_ne_coe]
  | coe m => simp only [← WithTop.coe_add, WithTop.coe_inj, add_right_inj]
end FourierJacobi.Measure

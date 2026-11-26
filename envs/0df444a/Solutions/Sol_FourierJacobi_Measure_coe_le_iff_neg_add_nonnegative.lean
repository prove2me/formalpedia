-- Prove2me | solution 1 for FourierJacobi.Measure.coe_le_iff_neg_add_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:50.801045+00:00
-- url     : https://prove2.me/submissions/1f5295b8-9eda-49f5-9b0f-8364bc37ed5a

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise WithZero
open FourierJacobi FourierJacobi.Measure
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.integerShells_t2Space
namespace FourierJacobi.Measure
theorem _root_.solution (n : ℤ) (v : WithTop ℤ) :
    (n : WithTop ℤ) ≤ v ↔ 0 ≤ ((-n : ℤ) : WithTop ℤ) + v := by
  induction v using WithTop.recTopCoe with
  | top => simp
  | coe m =>
    rw [← WithTop.coe_add]
    change (n : WithTop ℤ) ≤ (m : WithTop ℤ) ↔
      ((0 : ℤ) : WithTop ℤ) ≤ ((-n + m : ℤ) : WithTop ℤ)
    simp only [WithTop.coe_le_coe]
    omega
end FourierJacobi.Measure

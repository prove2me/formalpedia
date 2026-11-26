-- Prove2me | solution 1 for FourierJacobi.Measure.integerShell_eq_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:41:46.62245+00:00
-- url     : https://prove2.me/submissions/3b870b8e-9451-4c74-8b7d-4ce647b51be8

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
theorem _root_.solution (n : ℤ) :
    integerShell K n = integerBall K n \ integerBall K (n + 1) := by
  ext x
  simp only [integerShell, integerBall, Set.mem_ofPred_eq, Set.mem_sdiff]
  generalize localFieldValuation K x = v
  induction v using WithTop.recTopCoe with
  | top => simp
  | coe m =>
    simp only [WithTop.coe_inj, WithTop.coe_le_coe]
    omega
end FourierJacobi.Measure

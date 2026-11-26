-- Prove2me | solution 1 for FourierJacobi.Measure.exists_integerShell_iff_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:30.821773+00:00
-- url     : https://prove2.me/submissions/422bcccf-62ee-4b1d-b8df-ab2cc73fc655

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_ne_top
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
theorem _root_.solution (x : K) :
    (∃ n : ℤ, x ∈ integerShell K n) ↔ x ≠ 0 := by
  have hfinite (v : WithTop ℤ) : (∃ n : ℤ, v = (n : WithTop ℤ)) ↔ v ≠ ⊤ := by
    induction v using WithTop.recTopCoe with
    | top => simp
    | coe m => simp
  exact (hfinite (localFieldValuation K x)).trans (localFieldValuation_ne_top K x)
end FourierJacobi.Measure

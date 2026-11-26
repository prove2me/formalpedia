-- Prove2me | solution 1 for FourierJacobi.Measure.existsUnique_integerShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:36.726842+00:00
-- url     : https://prove2.me/submissions/8f5a0630-8b41-40ad-bd41-18e13fa45340

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Measure_integerShell_unique
import Theorems.Thm_FourierJacobi_Measure_exists_integerShell_iff_ne_zero

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
theorem _root_.solution (x : K) (hx : x ≠ 0) :
    ∃! n : ℤ, x ∈ integerShell K n := by
  obtain ⟨n, hn⟩ := (exists_integerShell_iff_ne_zero K x).mpr hx
  exact ⟨n, hn, fun m hm => integerShell_unique K x m n hm hn⟩
end FourierJacobi.Measure

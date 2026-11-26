-- Prove2me | solution 1 for FourierJacobi.Measure.integerBall_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:30.87479+00:00
-- url     : https://prove2.me/submissions/da1a8be5-8f29-41d2-9ffb-23e3924b6d21

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Measure_exists_integral_canonical_uniformizer
import Theorems.Thm_FourierJacobi_Measure_integerBall_eq_uniformizer_smul

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
theorem _root_.solution (n : ℤ) : IsOpen (integerBall K n) := by
  obtain ⟨π, hπ⟩ := exists_integral_canonical_uniformizer K
  rw [integerBall_eq_uniformizer_smul K π hπ n]
  exact (valuation K).isOpen_integer.smul _
end FourierJacobi.Measure

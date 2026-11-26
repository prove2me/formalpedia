-- Prove2me | solution 1 for FourierJacobi.Measure.unitValuationShell_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:34.749807+00:00
-- url     : https://prove2.me/submissions/60386646-010b-4d7a-9c48-4ecd8d36aeb9

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.Topology.Algebra.Group.Units
import Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
import Theorems.Thm_FourierJacobi_Measure_exists_integral_canonical_uniformizer


set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal Pointwise
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.multiplicativeHaar_t2Space
namespace FourierJacobi.Measure
theorem _root_.solution (n : ℤ) : IsCompact (unitValuationShell K n) := by
  obtain ⟨π, hπ⟩ := exists_integral_canonical_uniformizer K
  rw [unitValuationShell_eq_uniformizer_smul K π hπ n]
  exact (valuationRingUnits_isCompact K).smul _
end FourierJacobi.Measure

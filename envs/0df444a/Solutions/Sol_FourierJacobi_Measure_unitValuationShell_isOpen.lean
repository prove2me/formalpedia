-- Prove2me | solution 1 for FourierJacobi.Measure.unitValuationShell_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:37.21895+00:00
-- url     : https://prove2.me/submissions/3dee63f7-ab08-4e6c-ab27-57e941d7bd40

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
theorem _root_.solution (n : ℤ) : IsOpen (unitValuationShell K n) := by
  obtain ⟨π, hπ⟩ := exists_integral_canonical_uniformizer K
  rw [unitValuationShell_eq_uniformizer_smul K π hπ n]
  exact (valuationRingUnits_isOpen K).smul _
end FourierJacobi.Measure

-- Prove2me | solution 1 for FourierJacobi.Measure.unitValuationShell_pairwiseDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:40.68939+00:00
-- url     : https://prove2.me/submissions/844bda91-49c5-4e45-b32e-a0b7d616254a

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.Topology.Algebra.Group.Units
import Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
import Theorems.Thm_FourierJacobi_Measure_integerShell_unique


set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal Pointwise
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.multiplicativeHaar_t2Space
namespace FourierJacobi.Measure
theorem _root_.solution :
    Pairwise (fun m n : ℤ => Disjoint (unitValuationShell K m) (unitValuationShell K n)) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro u hm hn
  exact hmn (integerShell_unique K (u : K) m n hm hn)
end FourierJacobi.Measure

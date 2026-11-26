-- Prove2me | solution 1 for FourierJacobi.Measure.integerShell_pairwiseDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:52.021799+00:00
-- url     : https://prove2.me/submissions/dc8ed20b-c0df-4f3d-81fc-2ed7b7d31130

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Measure_integerShell_unique

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
theorem _root_.solution :
    Pairwise (fun m n : ℤ => Disjoint (integerShell K m) (integerShell K n)) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro x hm hn
  exact hmn (integerShell_unique K x m n hm hn)
end FourierJacobi.Measure

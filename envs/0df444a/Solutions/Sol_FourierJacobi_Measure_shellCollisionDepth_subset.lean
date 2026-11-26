-- Prove2me | solution 1 for FourierJacobi.Measure.shellCollisionDepth_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:39.386287+00:00
-- url     : https://prove2.me/submissions/afa73ba4-64be-48d6-8a12-a8146f313d46

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision

set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.shellCollision_t2Space
namespace FourierJacobi.Measure
theorem _root_.solution (a : K) (n : ℤ) (c : ℕ) :
    shellCollisionDepth K a n c ⊆ integerShell K n :=
  Set.Subset.trans Set.sdiff_subset Set.inter_subset_left
end FourierJacobi.Measure

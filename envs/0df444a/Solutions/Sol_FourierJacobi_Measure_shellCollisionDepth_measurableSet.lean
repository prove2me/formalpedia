-- Prove2me | solution 1 for FourierJacobi.Measure.shellCollisionDepth_measurableSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:52.39427+00:00
-- url     : https://prove2.me/submissions/1bdb4076-343b-4ae6-8d50-4a1c9311f4f5

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Theorems.Thm_FourierJacobi_Measure_shellCollisionTail_measurableSet

set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.shellCollision_t2Space
variable [MeasurableSpace K] [BorelSpace K]
namespace FourierJacobi.Measure
theorem _root_.solution (a : K) (n : ℤ) (c : ℕ) :
    MeasurableSet (shellCollisionDepth K a n c) :=
  (shellCollisionTail_measurableSet K a n c).diff
    (shellCollisionTail_measurableSet K a n (c + 1))
end FourierJacobi.Measure

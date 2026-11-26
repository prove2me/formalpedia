-- Prove2me | solution 1 for FourierJacobi.Measure.shellCollisionTail_measurableSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:30.86316+00:00
-- url     : https://prove2.me/submissions/f306fb44-8b14-4e88-9dc5-542267b137cc

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Theorems.Thm_FourierJacobi_Measure_integerBall_measurableSet
import Theorems.Thm_FourierJacobi_Measure_integerShell_measurableSet


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
    MeasurableSet (shellCollisionTail K a n c) :=
  (integerShell_measurableSet K n).inter
    ((integerBall_measurableSet K (n + c)).preimage (by fun_prop))
end FourierJacobi.Measure

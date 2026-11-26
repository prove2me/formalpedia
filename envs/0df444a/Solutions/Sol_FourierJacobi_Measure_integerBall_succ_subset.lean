-- Prove2me | solution 1 for FourierJacobi.Measure.integerBall_succ_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:33.422809+00:00
-- url     : https://prove2.me/submissions/dd2eeeae-e30c-4c7f-b5e1-c9665c3adcf6

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells

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
theorem _root_.solution (n : ℤ) : integerBall K (n + 1) ⊆ integerBall K n := by
  intro x hx
  change ((n + 1 : ℤ) : WithTop ℤ) ≤ localFieldValuation K x at hx
  change (n : WithTop ℤ) ≤ localFieldValuation K x
  exact le_trans (by exact_mod_cast (show n ≤ n + 1 by omega)) hx
end FourierJacobi.Measure

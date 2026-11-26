-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_integerShell_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:23.782032+00:00
-- url     : https://prove2.me/submissions/89d4020e-26c0-4a13-b0e9-452e1f357934

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Measure_integerShell_eq_sdiff
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_integerBall_ne_top

set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise WithZero
open FourierJacobi FourierJacobi.Measure
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.integerShells_t2Space
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Measure.integerShells_additiveHaar_regular
namespace FourierJacobi.Measure
theorem _root_.solution (n : ℤ) :
    additiveHaar K (integerShell K n) ≠ ⊤ := by
  rw [integerShell_eq_sdiff]
  exact measure_ne_top_of_subset Set.sdiff_subset (additiveHaar_integerBall_ne_top K n)
end FourierJacobi.Measure

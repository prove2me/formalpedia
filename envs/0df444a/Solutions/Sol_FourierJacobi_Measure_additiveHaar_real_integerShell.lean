-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_real_integerShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:19.262206+00:00
-- url     : https://prove2.me/submissions/191c9287-786f-48dc-813b-a7728fb7f82a

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Measure_integerShell_eq_sdiff
import Theorems.Thm_FourierJacobi_Measure_integerBall_succ_subset
import Theorems.Thm_FourierJacobi_Measure_integerBall_measurableSet
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_integerBall_ne_top
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_integerBall

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
    (additiveHaar K).real (integerShell K n) =
      (1 - (residueCardinality K : ℝ)⁻¹) * (residueCardinality K : ℝ) ^ (-n) := by
  rw [integerShell_eq_sdiff, measureReal_sdiff (integerBall_succ_subset K n)
    (integerBall_measurableSet K (n + 1)) (additiveHaar_integerBall_ne_top K n),
    additiveHaar_real_integerBall, additiveHaar_real_integerBall]
  have hq : (residueCardinality K : ℝ) ≠ 0 := by
    exact_mod_cast (residueCardinality_pos K).ne'
  rw [show -(n + 1) = -n + -1 by omega, zpow_add₀ hq, zpow_neg_one]
  ring
end FourierJacobi.Measure

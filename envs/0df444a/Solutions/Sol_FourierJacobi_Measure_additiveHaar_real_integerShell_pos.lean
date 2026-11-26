-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_real_integerShell_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:08.636802+00:00
-- url     : https://prove2.me/submissions/638cca6f-009d-4dd6-856e-7c9a6a0b13ea

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_integerShell
import Theorems.Thm_FourierJacobi_Measure_residueCardinality_one_lt


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
    0 < (additiveHaar K).real (integerShell K n) := by
  have hq : (1 : ℝ) < residueCardinality K := by exact_mod_cast residueCardinality_one_lt K
  have hq0 : (0 : ℝ) < residueCardinality K := lt_trans zero_lt_one hq
  rw [additiveHaar_real_integerShell]
  exact mul_pos (sub_pos.mpr ((inv_lt_one₀ hq0).mpr hq)) (zpow_pos hq0 _)
end FourierJacobi.Measure

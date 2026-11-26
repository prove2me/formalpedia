-- Prove2me | solution 1 for FourierJacobi.Measure.shellConditionalMass_collisionDepth_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:58.727922+00:00
-- url     : https://prove2.me/submissions/0bacdc43-53f5-4b5c-91b9-949ab1fbd2e8

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Theorems.Thm_FourierJacobi_Measure_shellCollisionTail_zero_eq
import Theorems.Thm_FourierJacobi_Measure_shellCollisionTail_succ_subset
import Theorems.Thm_FourierJacobi_Measure_shellCollisionDepth_subset
import Theorems.Thm_FourierJacobi_Measure_shellCollisionTail_measurableSet
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_shellCollisionTail
import Theorems.Thm_FourierJacobi_Measure_shellConditionalMass_of_subset
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_integerShell_ne_top
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_integerShell
import Theorems.Thm_FourierJacobi_Measure_residueCardinality_one_lt


set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.shellCollision_t2Space
variable [MeasurableSpace K] [BorelSpace K]
namespace FourierJacobi.Measure
theorem _root_.solution (a : K) (n : ℤ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) :
    shellConditionalMass K n (shellCollisionDepth K a n 0) =
      (residueCardinality K - 2) / (residueCardinality K - 1) := by
  have hq : (1 : ℝ) < residueCardinality K := by exact_mod_cast residueCardinality_one_lt K
  have hq0 : (0 : ℝ) < residueCardinality K := lt_trans zero_lt_one hq
  have hs : 1 - (residueCardinality K : ℝ)⁻¹ ≠ 0 :=
    (sub_pos.mpr ((inv_lt_one₀ hq0).mpr hq)).ne'
  rw [shellConditionalMass_of_subset K n _ (shellCollisionDepth_subset K a n 0),
    shellCollisionDepth,
    measureReal_sdiff (shellCollisionTail_succ_subset K a n 0)
      (shellCollisionTail_measurableSet K a n 1)
      (measure_ne_top_of_subset Set.inter_subset_left (additiveHaar_integerShell_ne_top K n)),
    shellCollisionTail_zero_eq K a n ha, additiveHaar_real_integerShell,
    additiveHaar_real_shellCollisionTail K a n 1 ha (by decide)]
  rw [Nat.cast_one, show -(n + 1) = -n + -1 by omega, zpow_add₀ hq0.ne', zpow_neg_one]
  field_simp
  ring
end FourierJacobi.Measure

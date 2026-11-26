-- Prove2me | solution 1 for FourierJacobi.Measure.shellConditionalMass_collisionDepth_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:57.533872+00:00
-- url     : https://prove2.me/submissions/a12bb53a-1932-4b1c-be80-b1d8667cc7c0

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Theorems.Thm_FourierJacobi_Measure_shellCollisionDepth_subset
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_shellCollisionDepth_pos
import Theorems.Thm_FourierJacobi_Measure_shellConditionalMass_of_subset
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
theorem _root_.solution (a : K) (n : ℤ) (c : ℕ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) (hc : 0 < c) :
    shellConditionalMass K n (shellCollisionDepth K a n c) =
      (residueCardinality K : ℝ) ^ (-(c : ℤ)) := by
  have hq : (1 : ℝ) < residueCardinality K := by exact_mod_cast residueCardinality_one_lt K
  have hq0 : (0 : ℝ) < residueCardinality K := lt_trans zero_lt_one hq
  have hs : 1 - (residueCardinality K : ℝ)⁻¹ ≠ 0 :=
    (sub_pos.mpr ((inv_lt_one₀ hq0).mpr hq)).ne'
  rw [shellConditionalMass_of_subset K n _ (shellCollisionDepth_subset K a n c),
    additiveHaar_real_shellCollisionDepth_pos K a n c ha hc,
    neg_add, zpow_add₀ hq0.ne']
  field_simp [sub_ne_zero.mpr hq.ne']
end FourierJacobi.Measure

-- Prove2me | solution 1 for FourierJacobi.Measure.shellCollisionTail_eq_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:44:24.033964+00:00
-- url     : https://prove2.me/submissions/dd0e1b02-65c1-49c4-b484-78db60e5da67

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.shellCollision_t2Space
namespace FourierJacobi.Measure
theorem _root_.solution (a : K) (n : ℤ) (c : ℕ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) (hc : 0 < c) :
    shellCollisionTail K a n c =
      (fun x : K => x - a) ⁻¹' integerBall K (n + c) := by
  apply Set.inter_eq_self_of_subset_right
  intro x hx
  change localFieldValuation K x = (n : WithTop ℤ)
  have hlt : localFieldValuation K a < localFieldValuation K (x - a) := by
    rw [ha]
    exact lt_of_lt_of_le (by exact_mod_cast (show n < n + (c : ℤ) by omega)) hx
  simpa only [sub_add_cancel, ha] using
    (localFieldValuation K).map_add_eq_of_lt_right hlt
end FourierJacobi.Measure

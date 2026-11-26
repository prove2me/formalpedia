-- Prove2me | solution 1 for FourierJacobi.Measure.shellCollisionDepth_eq_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:10.713994+00:00
-- url     : https://prove2.me/submissions/f53a4752-5831-45c0-a824-3e6cbb19a254

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Theorems.Thm_FourierJacobi_Measure_shellCollisionTail_eq_preimage
import Theorems.Thm_FourierJacobi_Measure_integerShell_eq_sdiff
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
    shellCollisionDepth K a n c =
      (fun x : K => x - a) ⁻¹' integerShell K (n + c) := by
  rw [shellCollisionDepth, shellCollisionTail_eq_preimage K a n c ha hc,
    shellCollisionTail_eq_preimage K a n (c + 1) ha (Nat.succ_pos c),
    ← Set.preimage_sdiff, integerShell_eq_sdiff]
  simp only [Nat.cast_add, Nat.cast_one, add_assoc]
end FourierJacobi.Measure

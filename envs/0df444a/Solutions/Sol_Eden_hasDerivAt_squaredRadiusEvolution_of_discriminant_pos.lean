-- Prove2me | solution 1 for Eden.hasDerivAt_squaredRadiusEvolution_of_discriminant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:09.270185+00:00
-- url     : https://prove2.me/submissions/b1deced4-5c13-4ed8-8592-311327154434

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_amplitudeSq_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.amplitudeSq_at_zero

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ}
    (hD : 0 < radialDiscriminant t s) :
    HasDerivAt (fun τ => squaredRadiusEvolution τ s)
      (-2 * squaredRadiusEvolution t s * (squaredRadiusEvolution t s - 1) *
        (squaredRadiusEvolution t s - 2)) t := by
  have he : HasDerivAt (fun τ : ℝ => Real.exp (-4 * τ))
      (Real.exp (-4 * t) * (-4)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-4 : ℝ)).exp
  have hd := he.add (((hasDerivAt_const t (1 : ℝ)).sub he).mul_const ((s - 1) ^ 2))
  have hr := hd.sqrt (ne_of_gt hD)
  have hR := Real.sqrt_pos.2 hD
  have hq := (hasDerivAt_const t (s - 1)).div hr (ne_of_gt hR)
  have hsq : Real.sqrt (radialDiscriminant t s) ^ 2 =
      Real.exp (-4 * t) + (1 - Real.exp (-4 * t)) * (s - 1) ^ 2 :=
    Real.sq_sqrt (le_of_lt hD)
  apply (hq.const_add 1).congr_deriv
  dsimp [squaredRadiusEvolution, radialDiscriminant] at hR hsq ⊢
  simp only [neg_mul] at hR hsq ⊢
  field_simp [ne_of_gt hR]
  nlinarith [congrArg (fun x : ℝ => (s - 1) * x) hsq]
end Eden

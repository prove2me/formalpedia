-- Prove2me | solution 1 for Eden.hasDerivAt_amplitudeSq_of_discriminant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:58.322604+00:00
-- url     : https://prove2.me/submissions/a52b4ca2-113b-4110-8058-e87ed7931a8c

import Definitions.Def_Eden_ScalarFlow
import Mathlib.Tactic.FunProp
import Definitions.Def_Eden_ScalarCalculus
import Theorems.Thm_Eden_continuous_radialDiscriminant_time
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_hasDerivAt_squaredRadiusEvolution_of_discriminant_pos
import Theorems.Thm_Eden_mul_amplitudeSq_of_discriminant_pos
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open scoped Topology
open Filter
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ}
    (hD : 0 < radialDiscriminant t s) :
    HasDerivAt (fun τ => amplitudeSq τ s)
      (2 * q (squaredRadiusEvolution t s) * amplitudeSq t s) t := by
  by_cases hs : s = 0
  · subst s
    have he : HasDerivAt (fun τ : ℝ => Real.exp (-4 * τ))
        (Real.exp (-4 * t) * (-4)) t := by
      simpa using ((hasDerivAt_id t).const_mul (-4 : ℝ)).exp
    norm_num [q, mul_comm] at he ⊢
    exact he
  have hpos : ∀ᶠ τ in 𝓝 t, 0 < radialDiscriminant τ s :=
    (continuous_radialDiscriminant_time s).continuousAt.eventually
      (Ioi_mem_nhds hD)
  have heq : (fun τ => amplitudeSq τ s) =ᶠ[𝓝 t]
      (fun τ => squaredRadiusEvolution τ s / s) := by
    filter_upwards [hpos] with τ hτ
    apply (eq_div_iff hs).2
    simpa only [mul_comm] using mul_amplitudeSq_of_discriminant_pos hτ
  have hder := ((hasDerivAt_squaredRadiusEvolution_of_discriminant_pos hD).div_const s).congr_of_eventuallyEq heq
  apply hder.congr_deriv
  rw [← mul_amplitudeSq_of_discriminant_pos hD]
  unfold q
  field_simp
end Eden

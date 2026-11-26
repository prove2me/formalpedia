-- Prove2me | solution 1 for Eden.hasDerivAt_radialAmplitude
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:07.901135+00:00
-- url     : https://prove2.me/submissions/c1d67519-af9d-4527-85ae-169493afcffd

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Eden_GrowthRates
import Theorems.Thm_Eden_hasDerivAt_sqrt_radialDiscriminant
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_hasDerivAt_planarAmplitude
import Theorems.Thm_Eden_planarAmplitude_pos
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_sqrt_radialDiscriminant_pos
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    HasDerivAt (fun τ => radialAmplitude τ s)
      (radialRate (squaredRadiusEvolution t s) * radialAmplitude t s) t := by
  have he : HasDerivAt (fun τ : ℝ => Real.exp (-4 * τ))
      (Real.exp (-4 * t) * (-4)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-4 : ℝ)).exp
  have hg := hasDerivAt_planarAmplitude ht hs
  have hr := hasDerivAt_sqrt_radialDiscriminant ht s
  have hp := planarAmplitude_pos ht hs
  have hR := sqrt_radialDiscriminant_pos ht s
  have hden := hg.mul (hr.pow 3)
  apply (he.div hden (ne_of_gt (mul_pos hp (pow_pos hR 3)))).congr_deriv
  dsimp [radialAmplitude, radialRate, q]
  field_simp [ne_of_gt hp, ne_of_gt hR]
  ring
end Eden

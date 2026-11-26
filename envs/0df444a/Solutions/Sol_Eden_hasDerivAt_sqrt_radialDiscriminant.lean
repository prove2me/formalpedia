-- Prove2me | solution 1 for Eden.hasDerivAt_sqrt_radialDiscriminant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:09.947706+00:00
-- url     : https://prove2.me/submissions/164b1664-6c30-4dae-ae37-bb5c39285c16

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Eden_GrowthRates
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_pos
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
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    HasDerivAt (fun τ => Real.sqrt (radialDiscriminant τ s))
      (-2 * (1 - (squaredRadiusEvolution t s - 1) ^ 2) *
        Real.sqrt (radialDiscriminant t s)) t := by
  have he : HasDerivAt (fun τ : ℝ => Real.exp (-4 * τ))
      (Real.exp (-4 * t) * (-4)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-4 : ℝ)).exp
  have hd := he.add (((hasDerivAt_const t (1 : ℝ)).sub he).mul_const ((s - 1) ^ 2))
  have hr := hd.sqrt (ne_of_gt (radialDiscriminant_pos ht s))
  have hR := sqrt_radialDiscriminant_pos ht s
  have hsq := Real.sq_sqrt (le_of_lt (radialDiscriminant_pos ht s))
  apply hr.congr_deriv
  change (Real.exp (-4 * t) * (-4) +
      (0 - Real.exp (-4 * t) * (-4)) * (s - 1) ^ 2) /
      (2 * Real.sqrt (radialDiscriminant t s)) = _
  dsimp only [squaredRadiusEvolution]
  field_simp [ne_of_gt hR]
  dsimp only [radialDiscriminant] at hsq ⊢
  simp only [neg_mul] at hsq ⊢
  nlinarith
end Eden

-- Prove2me | solution 1 for Eden.squaredRadiusEvolution_mem_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:15:32.874985+00:00
-- url     : https://prove2.me/submissions/f9b2b0b0-8b5f-4a94-adc1-1d20bed8d53f

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_Eden_RadialDynamics
import Theorems.Thm_Eden_radialDiscriminant_pos_on_interval
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (t : ℝ) {s : ℝ}
    (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) :
    squaredRadiusEvolution t s ∈ Set.Icc 0 2 := by
  have hD := radialDiscriminant_pos_on_interval t hs₀ hs₂
  have hR := Real.sqrt_pos.2 hD
  have hsq := Real.sq_sqrt hD.le
  have hu : (s - 1) ^ 2 ≤ 1 := by nlinarith
  have hm := mul_nonneg (sub_nonneg.mpr hu) (Real.exp_pos (-4 * t)).le
  have hbound : (s - 1) ^ 2 ≤ radialDiscriminant t s := by
    dsimp [radialDiscriminant]
    nlinarith
  have hl : -Real.sqrt (radialDiscriminant t s) ≤ s - 1 := by nlinarith
  have hr : s - 1 ≤ Real.sqrt (radialDiscriminant t s) := by nlinarith
  have hq₀ : -1 ≤ (s - 1) / Real.sqrt (radialDiscriminant t s) :=
    (le_div_iff₀ hR).2 (by linarith)
  have hq₂ : (s - 1) / Real.sqrt (radialDiscriminant t s) ≤ 1 :=
    (div_le_iff₀ hR).2 (by linarith)
  constructor <;> dsimp [squaredRadiusEvolution] <;> linarith
end Eden

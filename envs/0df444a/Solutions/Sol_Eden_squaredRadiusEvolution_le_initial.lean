-- Prove2me | solution 1 for Eden.squaredRadiusEvolution_le_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:09:45.64538+00:00
-- url     : https://prove2.me/submissions/2c67d8fb-4381-4733-b51d-0a1c298c459f

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_Eden_RadialDynamics
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
theorem _root_.solution {t s : ℝ} (ht : 0 ≤ t) (hs : 2 ≤ s) :
    squaredRadiusEvolution t s ≤ s := by
  have he : Real.exp (-4 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hD : 1 ≤ radialDiscriminant t s := by
    have hm := mul_nonneg (sub_nonneg.mpr he)
      (show 0 ≤ (s - 1) ^ 2 - 1 by nlinarith)
    dsimp [radialDiscriminant]
    nlinarith
  have hR : 1 ≤ Real.sqrt (radialDiscriminant t s) := by
    simpa using Real.sqrt_le_sqrt hD
  have hRp : 0 < Real.sqrt (radialDiscriminant t s) := by linarith
  have hdiv : (s - 1) / Real.sqrt (radialDiscriminant t s) ≤ s - 1 := by
    apply (div_le_iff₀ hRp).2
    nlinarith
  dsimp [squaredRadiusEvolution]
  linarith
end Eden

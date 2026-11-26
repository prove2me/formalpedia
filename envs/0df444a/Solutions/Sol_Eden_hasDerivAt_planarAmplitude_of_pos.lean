-- Prove2me | solution 1 for Eden.hasDerivAt_planarAmplitude_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:09:50.336472+00:00
-- url     : https://prove2.me/submissions/822ec20c-8ff6-474a-8fb9-23c570f754c7

import Definitions.Def_Eden_ScalarFlow
import Mathlib.Tactic.FunProp
import Definitions.Def_Eden_ScalarCalculus
import Theorems.Thm_Eden_hasDerivAt_amplitudeSq_of_discriminant_pos
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
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


attribute [local simp] Eden.planarAmplitude_zero_time

set_option autoImplicit true
noncomputable section
open scoped Topology
open Filter
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ}
    (hD : 0 < radialDiscriminant t s) (hB : 0 < amplitudeSq t s) :
    HasDerivAt (fun τ => planarAmplitude τ s)
      (q (squaredRadiusEvolution t s) * planarAmplitude t s) t := by
  have hg : 0 < planarAmplitude t s := Real.sqrt_pos.2 hB
  have hsq : planarAmplitude t s ^ 2 = amplitudeSq t s := Real.sq_sqrt hB.le
  apply ((hasDerivAt_amplitudeSq_of_discriminant_pos hD).sqrt (ne_of_gt hB)).congr_deriv
  dsimp [planarAmplitude] at hg hsq ⊢
  field_simp [ne_of_gt hg]
  nlinarith [congrArg (fun x : ℝ => q (squaredRadiusEvolution t s) * x) hsq]
end Eden

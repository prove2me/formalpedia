-- Prove2me | solution 1 for Eden.planarAmplitude_zero_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:06.75331+00:00
-- url     : https://prove2.me/submissions/70f73f54-a2ec-473f-85b1-ed9f00d19383

import Definitions.Def_Eden_ScalarFlow
import Mathlib.Tactic.FunProp
import Definitions.Def_Eden_ScalarCalculus
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



set_option autoImplicit true
noncomputable section
open scoped Topology
open Filter
open Eden
namespace Eden
theorem _root_.solution (s : ℝ) : planarAmplitude 0 s = 1 := by
  simp [planarAmplitude]
end Eden

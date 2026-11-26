-- Prove2me | solution 1 for Eden.squaredRadiusEvolution_surjOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:16.53889+00:00
-- url     : https://prove2.me/submissions/6ef19ab3-4ffe-461f-a07a-7f065d8e35a0

import Definitions.Def_Eden_InvariantSets
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Eden_StrictInvariance
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_hasDerivAt_squaredRadiusEvolution_parameter
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
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
open Eden
namespace Eden
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) :
    Set.SurjOn (squaredRadiusEvolution t) (Set.Icc 0 2) (Set.Icc 0 2) := by
  have hc : Continuous (squaredRadiusEvolution t) :=
    continuous_iff_continuousAt.2 fun s =>
      (hasDerivAt_squaredRadiusEvolution_parameter ht s).continuousAt
  have h := intermediate_value_Icc (show (0 : ℝ) ≤ 2 by norm_num) hc.continuousOn
  intro s hs
  exact h (by simpa only [squaredRadiusEvolution_at_zero,
    squaredRadiusEvolution_at_two] using hs)
end Eden

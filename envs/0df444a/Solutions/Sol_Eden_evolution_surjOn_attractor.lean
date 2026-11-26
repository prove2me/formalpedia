-- Prove2me | solution 1 for Eden.evolution_surjOn_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:14.566796+00:00
-- url     : https://prove2.me/submissions/0041194b-14dc-4d4b-b2e6-9b4e4d6d85a5

import Definitions.Def_Eden_InvariantSets
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Eden_StrictInvariance
import Theorems.Thm_Eden_planar_surjective_on_disc
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
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Set.SurjOn (evolution c t) attractor attractor := by
  intro p hp
  obtain ⟨u₁, v₁, h₁, hx₁, hy₁⟩ := planar_surjective_on_disc 1 ht hp.1
  obtain ⟨u₂, v₂, h₂, hx₂, hy₂⟩ := planar_surjective_on_disc (Real.sqrt 2) ht hp.2.1
  refine ⟨!₂[u₁, v₁, u₂, v₂, 0], ?_, ?_⟩
  · change u₁ ^ 2 + v₁ ^ 2 ≤ 2 ∧ u₂ ^ 2 + v₂ ^ 2 ≤ 2 ∧ (0 : ℝ) = 0
    exact ⟨h₁, h₂, rfl⟩
  · ext i
    fin_cases i <;>
      simp [evolution, hx₁, hy₁, hx₂, hy₂, hp.2.2]
end Eden

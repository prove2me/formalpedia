-- Prove2me | solution 1 for Eden.evolution_image_stationary_radii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:00:54.901599+00:00
-- url     : https://prove2.me/submissions/02b46615-f72d-42db-bcfe-2692623cb687

import Definitions.Def_Eden_InstabilityGeometry
import Definitions.Def_Eden_NonlinearInstability
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_surjOn_attractor
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_radiusEvolution_at_one
import Theorems.Thm_Eden_radiusEvolution_at_sqrt_two
import Theorems.Thm_Eden_radiusEvolution_at_zero
import Theorems.Thm_Eden_radiusEvolution_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_Eden_strictMono_squaredRadiusEvolution
import Theorems.Thm_P2M_Eden_radiusSq__evolution_4de951b85a7e
import Theorems.Thm_P2M_Eden_radiusSq__evolution_ce05ee2f5645
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_origin
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.radiusEvolution_at_one
attribute [local simp] Eden.radiusEvolution_at_sqrt_two
attribute [local simp] Eden.radiusEvolution_at_zero
attribute [local simp] Eden.radiusEvolution_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t a b : ℝ} (ht : 0 ≤ t)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    evolution c t '' {p | radiusSq₁ p = a ∧ radiusSq₂ p = b ∧ p 4 = 0} =
      {p | radiusSq₁ p = a ∧ radiusSq₂ p = b ∧ p 4 = 0} := by
  have hSa : squaredRadiusEvolution t a = a := by rcases ha with rfl | rfl <;> simp
  have hSb : squaredRadiusEvolution t b = b := by rcases hb with rfl | rfl <;> simp
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [radiusSq₁_evolution c ht, hp.1, hSa]
    · rw [radiusSq₂_evolution c ht, hp.2.1, hSb]
    · simp [evolution, hp.2.2]
  · intro hq
    have hqA : q ∈ attractor := by
      refine ⟨?_, ?_, hq.2.2⟩
      · rw [hq.1]; rcases ha with rfl | rfl <;> norm_num
      · rw [hq.2.1]; rcases hb with rfl | rfl <;> norm_num
    obtain ⟨p, hp, he⟩ := evolution_surjOn_attractor c ht hqA
    refine ⟨p, ⟨?_, ?_, hp.2.2⟩, he⟩
    · apply (strictMono_squaredRadiusEvolution ht).injective
      rw [hSa, ← radiusSq₁_evolution c ht, he, hq.1]
    · apply (strictMono_squaredRadiusEvolution ht).injective
      rw [hSb, ← radiusSq₂_evolution c ht, he, hq.2.1]
end Eden

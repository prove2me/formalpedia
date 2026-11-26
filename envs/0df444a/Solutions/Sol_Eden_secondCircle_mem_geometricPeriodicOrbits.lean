-- Prove2me | solution 1 for Eden.secondCircle_mem_geometricPeriodicOrbits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:07.272594+00:00
-- url     : https://prove2.me/submissions/5e40a3c5-bb11-431f-af8b-1fc7c7bb32f7

import Definitions.Def_Eden_CircleOrbits
import Mathlib.Data.Set.Card
import Definitions.Def_Eden_PeriodicOrbits
import Theorems.Thm_Eden_secondCircle_nonempty
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_forwardOrbit_eq_secondCircle
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_second_plane_return
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_Eden_vectorField_eq_zero_iff
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
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c s : ℝ} (hc : 0 < c)
    (hs : s = 1 ∨ s = 2) : secondCircle s ∈ geometricPeriodicOrbits c := by
  have hs₀ : 0 < s := by rcases hs with rfl | rfl <;> norm_num
  obtain ⟨p, hp⟩ := secondCircle_nonempty hs₀.le
  refine ⟨p, ⟨2 * Real.pi / Real.sqrt 2, by positivity,
    second_plane_return c hp.1 ?_ hp.2.2⟩, ?_, forwardOrbit_eq_secondCircle c hs hp⟩
  · exact hs.imp (hp.2.1.trans ·) (hp.2.1.trans ·)
  · intro heq
    have hz := (vectorField_eq_zero_iff (ne_of_gt hc) p).mp heq
    have hr : radiusSq₂ p = 0 := by simp [hz, radiusSq₂]
    linarith [hp.2.1]
end Eden

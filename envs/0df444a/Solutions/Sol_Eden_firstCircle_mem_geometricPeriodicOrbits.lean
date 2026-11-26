-- Prove2me | solution 1 for Eden.firstCircle_mem_geometricPeriodicOrbits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:03.597523+00:00
-- url     : https://prove2.me/submissions/b3d0cb30-744e-4cec-bc83-e0871787c930

import Definitions.Def_Eden_CircleOrbits
import Mathlib.Data.Set.Card
import Definitions.Def_Eden_PeriodicOrbits
import Theorems.Thm_Eden_firstCircle_nonempty
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_first_plane_return
import Theorems.Thm_Eden_forwardOrbit_eq_firstCircle
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
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
    (hs : s = 1 ∨ s = 2) : firstCircle s ∈ geometricPeriodicOrbits c := by
  have hs₀ : 0 < s := by rcases hs with rfl | rfl <;> norm_num
  obtain ⟨p, hp⟩ := firstCircle_nonempty hs₀.le
  refine ⟨p, ⟨2 * Real.pi, by positivity, first_plane_return c ?_ hp.2.1 hp.2.2⟩,
    ?_, forwardOrbit_eq_firstCircle c hs hp⟩
  · exact hs.imp (hp.1.trans ·) (hp.1.trans ·)
  · intro heq
    have hz := (vectorField_eq_zero_iff (ne_of_gt hc) p).mp heq
    have hr : radiusSq₁ p = 0 := by simp [hz, radiusSq₁]
    linarith [hp.1]
end Eden

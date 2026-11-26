-- Prove2me | solution 1 for Eden.geometricPeriodicOrbits_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:21:55.725353+00:00
-- url     : https://prove2.me/submissions/b4a0819b-138c-4a17-ba30-33c328f7af27

import Definitions.Def_Eden_CircleOrbits
import Mathlib.Data.Set.Card
import Definitions.Def_Eden_PeriodicOrbits
import Theorems.Thm_Eden_firstCircle_mem_geometricPeriodicOrbits
import Theorems.Thm_Eden_secondCircle_mem_geometricPeriodicOrbits
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_forwardOrbit_eq_firstCircle
import Theorems.Thm_Eden_forwardOrbit_eq_secondCircle
import Theorems.Thm_Eden_mem_positiveReturnSet_iff
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
theorem _root_.solution {c : ℝ} (hc : 0 < c) :
    geometricPeriodicOrbits c = {firstCircle 1, firstCircle 2, secondCircle 1, secondCircle 2} := by
  ext O
  constructor
  · rintro ⟨p, hp, hne, hO⟩
    rcases (mem_positiveReturnSet_iff hc p).mp hp with rfl | h | h | h | h
    · exact False.elim (hne ((vectorField_eq_zero_iff (ne_of_gt hc) 0).mpr rfl))
    · have hcircle := hO.symm.trans (forwardOrbit_eq_firstCircle c (Or.inl rfl) h)
      simp [hcircle]
    · have hcircle := hO.symm.trans (forwardOrbit_eq_firstCircle c (Or.inr rfl) h)
      simp [hcircle]
    · have hcircle := hO.symm.trans (forwardOrbit_eq_secondCircle c (Or.inl rfl) h)
      simp [hcircle]
    · have hcircle := hO.symm.trans (forwardOrbit_eq_secondCircle c (Or.inr rfl) h)
      simp [hcircle]
  · intro h
    simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact firstCircle_mem_geometricPeriodicOrbits hc (Or.inl rfl)
    · exact firstCircle_mem_geometricPeriodicOrbits hc (Or.inr rfl)
    · exact secondCircle_mem_geometricPeriodicOrbits hc (Or.inl rfl)
    · exact secondCircle_mem_geometricPeriodicOrbits hc (Or.inr rfl)
end Eden

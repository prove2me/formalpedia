-- Prove2me | solution 1 for Eden.mem_positiveReturnSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:20:34.272773+00:00
-- url     : https://prove2.me/submissions/de4f9ff1-843e-4d7b-9b11-f04bbae3551c

import Definitions.Def_Eden_RotationReturns
import Definitions.Def_Eden_PeriodicSets
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_eq_zero_of_radii_and_fifth_zero
import Theorems.Thm_Eden_first_plane_return
import Theorems.Thm_Eden_second_plane_return
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_fifth_eq_zero_of_evolution_return
import Theorems.Thm_Eden_one_radius_zero_of_evolution_return
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
import Theorems.Thm_Eden_stationary_radii_of_evolution_return
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
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


attribute [local simp] Eden.evolution_origin

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 0 < c) (p : PhaseSpace) :
    p ∈ positiveReturnSet c ↔ p = 0 ∨ p ∈ firstCircle 1 ∨ p ∈ firstCircle 2 ∨
      p ∈ secondCircle 1 ∨ p ∈ secondCircle 2 := by
  constructor
  · rintro ⟨t, ht, hret⟩
    have hs := stationary_radii_of_evolution_return c ht hret
    have hw := fifth_eq_zero_of_evolution_return hc ht hret
    rcases one_radius_zero_of_evolution_return c ht hret with h₁ | h₂
    · rcases hs.2 with h₂ | h₂ | h₂
      · exact Or.inl (eq_zero_of_radii_and_fifth_zero h₁ h₂ hw)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h₁, h₂, hw⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h₁, h₂, hw⟩)))
    · rcases hs.1 with h₁ | h₁ | h₁
      · exact Or.inl (eq_zero_of_radii_and_fifth_zero h₁ h₂ hw)
      · exact Or.inr (Or.inl ⟨h₁, h₂, hw⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h₁, h₂, hw⟩))
  · rintro (rfl | h | h | h | h)
    · exact ⟨1, by norm_num, evolution_origin c 1⟩
    · exact ⟨2 * Real.pi, by positivity, first_plane_return c (Or.inl h.1) h.2.1 h.2.2⟩
    · exact ⟨2 * Real.pi, by positivity, first_plane_return c (Or.inr h.1) h.2.1 h.2.2⟩
    · exact ⟨2 * Real.pi / Real.sqrt 2, by positivity,
        second_plane_return c h.1 (Or.inl h.2.1) h.2.2⟩
    · exact ⟨2 * Real.pi / Real.sqrt 2, by positivity,
        second_plane_return c h.1 (Or.inr h.2.1) h.2.2⟩
end Eden

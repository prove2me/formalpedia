-- Prove2me | solution 1 for Eden.volumeDefect_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:02.925966+00:00
-- url     : https://prove2.me/submissions/d5a9230f-bd9b-4d57-8e43-eb6f5b0e0cec

import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_VolumeGrowth
import Theorems.Thm_Eden_radialDefect_nonneg
import Theorems.Thm_Eden_radialDefect_at_one
import Theorems.Thm_Eden_radialDefect_eq_zero_iff
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
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
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
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


attribute [local simp] Eden.radialDefect_at_one

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) : volumeDefect t p = 0 ↔ p ∈ torus := by
  have h₁ := radialDefect_nonneg ht.le (radiusSq₁ p)
  have h₂ := radialDefect_nonneg ht.le (radiusSq₂ p)
  constructor
  · intro hz
    have hz₁ : radialDefect t (radiusSq₁ p) = 0 := by dsimp [volumeDefect] at hz; linarith
    have hz₂ : radialDefect t (radiusSq₂ p) = 0 := by dsimp [volumeDefect] at hz; linarith
    exact ⟨(radialDefect_eq_zero_iff ht).1 hz₁,
      (radialDefect_eq_zero_iff ht).1 hz₂, hp.2.2⟩
  · intro hT
    simp [volumeDefect, hT.1, hT.2.1]
end Eden

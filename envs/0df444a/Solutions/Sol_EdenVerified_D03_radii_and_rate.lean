-- Prove2me | solution 1 for EdenVerified.D03_radii_and_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:15.183583+00:00
-- url     : https://prove2.me/submissions/72b357f2-1b53-479c-8bcb-89e4e394bb58

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_frequencyEvolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarDiagonal_apply
import Theorems.Thm_Eden_planarMovingPerturbation_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDefect_at_one
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_radiusEvolution_at_one
import Theorems.Thm_Eden_radiusEvolution_at_sqrt_two
import Theorems.Thm_Eden_radiusEvolution_at_zero
import Theorems.Thm_Eden_radiusEvolution_zero_time
import Theorems.Thm_Eden_singularValueFunction_zero
import Theorems.Thm_Eden_spectralProduct_zero
import Theorems.Thm_Eden_spectrumInterpolation_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_P2M_Eden_radiusSq__nonneg_5272e4fb8458
import Theorems.Thm_P2M_Eden_radiusSq__nonneg_7729c3bfdb8d
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_origin
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.frequencyEvolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarDiagonal_apply
attribute [local simp] Eden.planarMovingPerturbation_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDefect_at_one
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.radiusEvolution_at_one
attribute [local simp] Eden.radiusEvolution_at_sqrt_two
attribute [local simp] Eden.radiusEvolution_at_zero
attribute [local simp] Eden.radiusEvolution_zero_time
attribute [local simp] Eden.singularValueFunction_zero
attribute [local simp] Eden.spectralProduct_zero
attribute [local simp] Eden.spectrumInterpolation_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (p : PhaseSpace) :
    (radiusSq₁ p = p 0 ^ 2 + p 1 ^ 2) ∧
    (radiusSq₂ p = p 2 ^ 2 + p 3 ^ 2) ∧
    0 ≤ radiusSq₁ p ∧ 0 ≤ radiusSq₂ p ∧
    (‖(⟨p 0, p 1⟩ : ℂ)‖ ^ 2 = radiusSq₁ p) ∧
    (‖(⟨p 2, p 3⟩ : ℂ)‖ ^ 2 = radiusSq₂ p) ∧
    (‖(⟨p 0, p 1⟩ : ℂ)‖ = Real.sqrt (radiusSq₁ p)) ∧
    (‖(⟨p 2, p 3⟩ : ℂ)‖ = Real.sqrt (radiusSq₂ p)) ∧
    0 ≤ Real.sqrt (radiusSq₁ p) ∧ 0 ≤ Real.sqrt (radiusSq₂ p) ∧
    (∀ s : ℝ, q s = -(s - 1) * (s - 2) ∧ q s = -s ^ 2 + 3 * s - 2) ∧
    0 < Real.sqrt 2 := by
  have h₁ : Complex.normSq (⟨p 0, p 1⟩ : ℂ) = radiusSq₁ p := by
    simp [Complex.normSq_apply, radiusSq₁, pow_two]
  have h₂ : Complex.normSq (⟨p 2, p 3⟩ : ℂ) = radiusSq₂ p := by
    simp [Complex.normSq_apply, radiusSq₂, pow_two]
  refine ⟨rfl, rfl, radiusSq₁_nonneg p, radiusSq₂_nonneg p, ?_, ?_, ?_, ?_,
    Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_, by positivity⟩
  · exact (Complex.normSq_eq_norm_sq _).symm.trans h₁
  · exact (Complex.normSq_eq_norm_sq _).symm.trans h₂
  · rw [Complex.norm_def, h₁]
  · rw [Complex.norm_def, h₂]
  · intro s
    exact ⟨rfl, by unfold q; ring⟩
end EdenVerified

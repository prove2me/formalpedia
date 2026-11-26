-- Prove2me | solution 1 for EdenVerified.p29_two_two_limits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:22:36.814906+00:00
-- url     : https://prove2.me/submissions/c49320c2-133e-45db-a530-e88cfaee3393

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_descending_radiusPairSpectrum_two_two
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_frequencyEvolution_zero_time
import Theorems.Thm_Eden_kaplanYorkeDimension_two_two
import Theorems.Thm_Eden_lyapunovExponent_eq_of_limiting_radii
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
import Theorems.Thm_Eden_tendsto_finiteTimeDimension
import Theorems.Thm_Eden_tendsto_lyapunovExponent
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
theorem _root_.solution (c : ℝ) (hc : 4 < c) (p : PhaseSpace) (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 2)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 2) :
    (∀ i : Fin 5, i.val < 2 →
      Tendsto (fun t : ℝ => normalizedLogSingularValues c t p i) atTop (𝓝 0)) ∧
    Tendsto (fun t : ℝ => normalizedLogSingularValues c t p 2) atTop (𝓝 (-4)) ∧
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 2) := by
  have hs := (lyapunovExponent_eq_of_limiting_radii c p (Or.inl ⟨h₁, h₂⟩)).trans
    (descending_radiusPairSpectrum_two_two hc)
  have hdim : asymptoticDimension c p = 2 := by
    rw [asymptoticDimension, hs, kaplanYorkeDimension_two_two hc]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have he : lyapunovExponent c p i = 0 := by
      rw [hs]
      fin_cases i <;> norm_num at *
    simpa only [normalizedLogSingularValues, he] using tendsto_lyapunovExponent c p i
  · simpa [normalizedLogSingularValues, hs] using tendsto_lyapunovExponent c p 2
  · simpa only [hdim] using tendsto_finiteTimeDimension hc hp
end EdenVerified

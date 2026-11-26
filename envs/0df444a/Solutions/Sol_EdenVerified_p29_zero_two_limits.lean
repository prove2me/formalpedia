-- Prove2me | solution 1 for EdenVerified.p29_zero_two_limits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:22:34.832805+00:00
-- url     : https://prove2.me/submissions/9e6b8f9d-86e4-4655-b6e6-4633f6344cfe

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_two
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_frequencyEvolution_zero_time
import Theorems.Thm_Eden_kaplanYorkeDimension_zero_two
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
    (hpair : (limitingSquaredRadius (radiusSq₁ p) = 0 ∧ limitingSquaredRadius (radiusSq₂ p) = 2) ∨
      (limitingSquaredRadius (radiusSq₁ p) = 2 ∧ limitingSquaredRadius (radiusSq₂ p) = 0)) :
    Tendsto (fun t : ℝ => normalizedLogSingularValues c t p 0) atTop (𝓝 0) ∧
    Tendsto (fun t : ℝ => normalizedLogSingularValues c t p 1) atTop (𝓝 (-2)) ∧
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 1) := by
  have hs := (lyapunovExponent_eq_of_limiting_radii c p hpair).trans
    (descending_radiusPairSpectrum_zero_two hc)
  have hdim : asymptoticDimension c p = 1 := by
    rw [asymptoticDimension, hs, kaplanYorkeDimension_zero_two hc]
  refine ⟨?_, ?_, ?_⟩
  · simpa [normalizedLogSingularValues, hs] using tendsto_lyapunovExponent c p 0
  · simpa [normalizedLogSingularValues, hs] using tendsto_lyapunovExponent c p 1
  · simpa only [hdim] using tendsto_finiteTimeDimension hc hp
end EdenVerified

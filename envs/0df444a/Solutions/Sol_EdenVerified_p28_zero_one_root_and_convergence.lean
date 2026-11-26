-- Prove2me | solution 1 for EdenVerified.p28_zero_one_root_and_convergence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:22:18.776391+00:00
-- url     : https://prove2.me/submissions/e16a4390-83b5-4756-8cf9-46e545a3eff1

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_one
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_frequencyEvolution_zero_time
import Theorems.Thm_Eden_kaplanYorkeDimension_zero_one
import Theorems.Thm_Eden_lyapunovExponent_antitone
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
import Theorems.Thm_Eden_spectrumInterpolation_neg_iff
import Theorems.Thm_Eden_spectrumInterpolation_pos_zero_one
import Theorems.Thm_Eden_spectrumInterpolation_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_Eden_tendsto_finiteTimeDimension
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
theorem _root_.solution (c : ℝ) (hc : 4 < c)
    (p : PhaseSpace) (hp : p ∈ attractor)
    (hpair : (limitingSquaredRadius (radiusSq₁ p) = 0 ∧ limitingSquaredRadius (radiusSq₂ p) = 1) ∨
      (limitingSquaredRadius (radiusSq₁ p) = 1 ∧ limitingSquaredRadius (radiusSq₂ p) = 0)) :
    (∀ d : ℝ, d ∈ Ioo 0 3 → 0 < spectrumInterpolation (lyapunovExponent c p) d) ∧
    spectrumInterpolation (lyapunovExponent c p) 3 = 0 ∧
    (∀ d : ℝ, d ∈ Ioc 3 5 → spectrumInterpolation (lyapunovExponent c p) d < 0) ∧
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 3) := by
  have hs := (lyapunovExponent_eq_of_limiting_radii c p hpair).trans
    (descending_radiusPairSpectrum_zero_one hc)
  have hdim : asymptoticDimension c p = 3 := by
    rw [asymptoticDimension, hs, kaplanYorkeDimension_zero_one hc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hd
    rw [hs]
    exact spectrumInterpolation_pos_zero_one hd
  · rw [hs]
    norm_num [spectrumInterpolation, singularWeight, Fin.sum_univ_succ]
  · intro d hd
    apply (spectrumInterpolation_neg_iff (lyapunovExponent_antitone c p)
      (show d ∈ Icc 0 5 from ⟨by linarith [hd.1], hd.2⟩)).mpr
    change asymptoticDimension c p < d
    rw [hdim]
    exact hd.1
  · simpa only [hdim] using tendsto_finiteTimeDimension hc hp
end EdenVerified

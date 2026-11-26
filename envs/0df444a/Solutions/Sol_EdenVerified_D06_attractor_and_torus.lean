-- Prove2me | solution 1 for EdenVerified.D06_attractor_and_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:51.956723+00:00
-- url     : https://prove2.me/submissions/a2b8d197-8980-40cd-9f2f-fe759274c3e4

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_attractor_nonempty
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_frequencyEvolution_zero_time
import Theorems.Thm_Eden_isCompact_attractor
import Theorems.Thm_Eden_isCompact_torus
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
import Theorems.Thm_Eden_torus_nonempty
import Theorems.Thm_Eden_torus_subset_attractor
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
theorem _root_.solution :
    attractor = {p : PhaseSpace | radiusSq₁ p ≤ 2 ∧ radiusSq₂ p ≤ 2 ∧ p 4 = 0} ∧
    torus = {p : PhaseSpace | radiusSq₁ p = 1 ∧ radiusSq₂ p = 1 ∧ p 4 = 0} ∧
    attractor = {p : PhaseSpace | Real.sqrt (radiusSq₁ p) ≤ Real.sqrt 2 ∧
      Real.sqrt (radiusSq₂ p) ≤ Real.sqrt 2 ∧ p 4 = 0} ∧
    torus = {p : PhaseSpace | Real.sqrt (radiusSq₁ p) = 1 ∧
      Real.sqrt (radiusSq₂ p) = 1 ∧ p 4 = 0} ∧
    attractor.Nonempty ∧ IsCompact attractor ∧
    torus.Nonempty ∧ IsCompact torus ∧ torus ⊆ attractor := by
  refine ⟨rfl, rfl, ?_, ?_, attractor_nonempty, isCompact_attractor,
    torus_nonempty, isCompact_torus, torus_subset_attractor⟩
  · ext p
    simp only [attractor, mem_ofPred_eq, Real.sqrt_le_sqrt_iff (by norm_num : (0 : ℝ) ≤ 2)]
  · ext p
    simp only [torus, mem_ofPred_eq, Real.sqrt_eq_one]
end EdenVerified

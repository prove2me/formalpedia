-- Prove2me | solution 1 for Eden.finiteTimeDimension_eq_target_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:07:34.201872+00:00
-- url     : https://prove2.me/submissions/d3178312-6abd-4fe4-a64b-b2b09abdc91c

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
import Theorems.Thm_Eden_singularValueFunction_evolution_at_target
import Theorems.Thm_Eden_finiteTimeDimension_le_target
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_finiteTimeDimension_isGreatest
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDefect_at_one
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_singularValueFunction_zero
import Theorems.Thm_Eden_spectralProduct_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_Eden_targetDimension_bounds
import Theorems.Thm_Eden_volumeDefect_eq_zero_iff
import Theorems.Thm_Eden_volumeDefect_nonneg
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
attribute [local simp] Eden.radialDefect_at_one
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.singularValueFunction_zero
attribute [local simp] Eden.spectralProduct_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    finiteTimeDimension c t p = targetDimension c ↔ p ∈ torus := by
  constructor
  · intro heq
    have hmem := (finiteTimeDimension_isGreatest c ht.le p).1.2
    rw [heq, singularValueFunction_evolution_at_target hc ht.le hp] at hmem
    have hlog : 0 ≤ -6 * volumeDefect t p := Real.one_le_exp_iff.mp hmem
    exact (volumeDefect_eq_zero_iff ht hp).1 (by linarith [volumeDefect_nonneg ht.le p])
  · intro hT
    apply le_antisymm (finiteTimeDimension_le_target hc ht hp)
    apply (finiteTimeDimension_isGreatest c ht.le p).2
    refine ⟨⟨by linarith [(targetDimension_bounds hc).1], (targetDimension_bounds hc).2.le⟩, ?_⟩
    rw [singularValueFunction_evolution_at_target hc ht.le hp,
      (volumeDefect_eq_zero_iff ht hp).2 hT]
    simp
end Eden

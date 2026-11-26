-- Prove2me | solution 1 for Eden.spectrumInterpolation_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:09:27.940376+00:00
-- url     : https://prove2.me/submissions/1b316e83-1a59-4a0e-a08c-849ee522c14b

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SingularValueFunction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Definitions.Def_Eden_LogarithmicInterpolation
import Theorems.Thm_Eden_singularWeight_bounds
import Theorems.Thm_Eden_spectrumInterpolation_zero
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
import Theorems.Thm_Eden_singularValueFunction_zero
import Theorems.Thm_Eden_spectralProduct_zero
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
attribute [local simp] Eden.singularValueFunction_zero
attribute [local simp] Eden.spectralProduct_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time


attribute [local simp] Eden.spectrumInterpolation_zero

set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (a b : Fin 5 → ℝ) (d : ℝ) :
    dist (spectrumInterpolation a d) (spectrumInterpolation b d) ≤ 5 * dist a b := by
  rw [Real.dist_eq]
  unfold spectrumInterpolation
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin 5, |singularWeight i d * a i - singularWeight i d * b i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 5, dist a b := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub, abs_mul, abs_of_nonneg (singularWeight_bounds i d).1]
      calc
        _ ≤ |a i - b i| := mul_le_of_le_one_left (abs_nonneg _) (singularWeight_bounds i d).2
        _ ≤ dist a b := by simpa only [Real.dist_eq] using dist_le_pi_dist a b i
    _ = _ := by simp
end Eden

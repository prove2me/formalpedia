-- Prove2me | solution 1 for Eden.spectrumInterpolation_interpolate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:54:04.729982+00:00
-- url     : https://prove2.me/submissions/ce553642-f9b3-4210-ad8a-f8c04a9bb0c8

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SingularValueFunction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Definitions.Def_Eden_LogarithmicInterpolation
import Theorems.Thm_Eden_spectrumInterpolation_eq_range
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
import Theorems.Thm_Eden_singularWeight_eq_fraction
import Theorems.Thm_Eden_singularWeight_eq_one
import Theorems.Thm_Eden_singularWeight_eq_zero
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



set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (a : Fin 5 → ℝ) {k : ℕ} (hk : k < 5)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    spectrumInterpolation a ((k : ℝ) + α) =
      spectrumPartialSum a k + α * spectrumEntry a k := by
  rw [spectrumInterpolation_eq_range]
  have htrunc : (∑ i ∈ Finset.range (k + 1),
      singularWeight i ((k : ℝ) + α) * spectrumEntry a i) =
      ∑ i ∈ Finset.range 5, singularWeight i ((k : ℝ) + α) * spectrumEntry a i := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i hi hnot
    have hki : k < i := by simp only [Finset.mem_range] at hnot; omega
    rw [singularWeight_eq_zero hki hα₁, zero_mul]
  rw [← htrunc, Finset.sum_range_succ, singularWeight_eq_fraction k hα₀ hα₁]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [singularWeight_eq_one (Finset.mem_range.mp hi) hα₀, one_mul]
end Eden

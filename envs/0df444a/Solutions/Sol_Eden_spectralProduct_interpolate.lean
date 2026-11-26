-- Prove2me | solution 1 for Eden.spectralProduct_interpolate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:19.975434+00:00
-- url     : https://prove2.me/submissions/b581b0f4-bd1e-475c-9b2b-79a70589f292

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
import Theorems.Thm_Eden_singularWeight_eq_one
import Theorems.Thm_Eden_singularWeight_eq_fraction
import Theorems.Thm_Eden_singularWeight_eq_zero
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



set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (a : ℕ → ℝ) {n k : ℕ} (hk : k < n)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    spectralProduct n a ((k : ℝ) + α) =
      (∏ i ∈ Finset.range k, a i) * a k ^ α := by
  unfold spectralProduct
  have htrunc : (∏ i ∈ Finset.range (k + 1), a i ^ singularWeight i ((k : ℝ) + α)) =
      ∏ i ∈ Finset.range n, a i ^ singularWeight i ((k : ℝ) + α) := by
    apply Finset.prod_subset (Finset.range_mono (by omega))
    intro i hi hnot
    have hki : k < i := by simp only [Finset.mem_range] at hnot; omega
    rw [singularWeight_eq_zero hki hα₁, Real.rpow_zero]
  rw [← htrunc, Finset.prod_range_succ, singularWeight_eq_fraction k hα₀ hα₁]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [singularWeight_eq_one (Finset.mem_range.mp hi) hα₀, Real.rpow_one]
end Eden

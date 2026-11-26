-- Prove2me | solution 1 for FD1D.finite_average_sqrt_le_sqrt_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:01:37.741185+00:00
-- url     : https://prove2.me/submissions/c7bbeee6-4d5d-42d6-a530-674821708ba7

import Definitions.Def_FD1D_Potential
import Definitions.Def_FD1D_Parameters
import Definitions.Def_FD1D_PotentialBounds
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_harmonicPotential_zero
import Theorems.Thm_FD1D_leafCount_eq_pow
import Theorems.Thm_FD1D_natFloor_parameterRatio
import Theorems.Thm_FD1D_policyA_eq_parameterA
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.harmonicPotential_zero
attribute [local simp] FD1D.leafCount_eq_pow
attribute [local simp] FD1D.natFloor_parameterRatio
attribute [local simp] FD1D.policyA_eq_parameterA
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D
noncomputable section
open Set intervalIntegral
open scoped BigOperators
namespace FD1D
theorem _root_.solution
    {T : ℕ} (hT : 0 < T) (f : ℕ → ℝ)
    (hf : ∀ t < T, 0 ≤ f t) :
    (∑ t ∈ Finset.range T, Real.sqrt (f t)) / T ≤
      Real.sqrt ((∑ t ∈ Finset.range T, f t) / T) := by
  let w : ℕ → ℝ := fun _ => 1 / (T : ℝ)
  have hw0 : ∀ t ∈ Finset.range T, 0 ≤ w t := by
    intro t ht
    dsimp [w]
    positivity
  have hw1 : ∑ t ∈ Finset.range T, w t = 1 := by
    simp [w, hT.ne']
  have hmem : ∀ t ∈ Finset.range T, f t ∈ Ici (0 : ℝ) := by
    intro t ht
    exact hf t (Finset.mem_range.mp ht)
  have hjensen :=
    Real.strictConcaveOn_sqrt.concaveOn.le_map_sum
      hw0 hw1 hmem
  calc
    (∑ t ∈ Finset.range T, Real.sqrt (f t)) / T =
        ∑ t ∈ Finset.range T, w t * Real.sqrt (f t) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro t ht
      simp only [w, div_eq_mul_inv, one_mul]
      ring
    _ ≤ Real.sqrt (∑ t ∈ Finset.range T, w t * f t) := by
      simpa only [smul_eq_mul, Function.comp_apply] using hjensen
    _ = Real.sqrt ((∑ t ∈ Finset.range T, f t) / T) := by
      congr 1
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro t ht
      simp only [w, div_eq_mul_inv, one_mul]
      ring
end FD1D

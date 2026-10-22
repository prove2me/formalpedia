-- Prove2me | solution 1 for BirkhoffGlobalSection.inner_collinear_polynomial_root_is_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:42:53.04779+00:00
-- url     : https://prove2.me/submissions/d6e7400e-e6d5-4c00-9c35-bb7bb68ed7e2

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Theorems.Thm_BirkhoffGlobalSection_jacobi_collisionFree_differentiableAt
import Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_position_one
import Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_position_two
import Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_momentum_one
import Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_momentum_two

open BirkhoffGlobalSection

theorem solution (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (x : ℝ)
    (hxlo : -μ < x) (hxhi : x < 1 - μ)
    (hpoly : x * (x + μ) ^ 2 * (1 - μ - x) ^ 2 -
      (1 - μ) * (1 - μ - x) ^ 2 + μ * (x + μ) ^ 2 = 0) :
    IsInnerLagrangePoint μ (![x, 0, 0, -x] : Phase) := by
  let L : Phase := ![x, 0, 0, -x]
  have hr : 0 < x + μ := by linarith
  have hd : 0 < 1 - μ - x := by linarith
  have hfree : collisionFree μ L := by
    change 0 < (x + μ) ^ 2 + (0 : ℝ) ^ 2 ∧
      0 < (x - 1 + μ) ^ 2 + (0 : ℝ) ^ 2
    constructor
    · nlinarith [sq_pos_of_pos hr]
    · have hne : x - 1 + μ ≠ 0 := by linarith
      nlinarith [sq_pos_of_ne_zero hne]
  have hdiff := jacobi_collisionFree_differentiableAt μ L hfree
  have hbal : x = (1 - μ) / (x + μ) ^ 2 - μ / (1 - μ - x) ^ 2 := by
    have hrne : x + μ ≠ 0 := ne_of_gt hr
    have hdne : 1 - μ - x ≠ 0 := ne_of_gt hd
    field_simp
    nlinarith [hpoly]
  have hroot₁ : Real.sqrt ((L 0 + μ) ^ 2 + (L 1) ^ 2) = x + μ := by
    change Real.sqrt ((x + μ) ^ 2 + (0 : ℝ) ^ 2) = x + μ
    simp [Real.sqrt_sq_eq_abs, abs_of_pos hr]
  have hroot₂ : Real.sqrt ((L 0 - 1 + μ) ^ 2 + (L 1) ^ 2) = 1 - μ - x := by
    change Real.sqrt ((x - 1 + μ) ^ 2 + (0 : ℝ) ^ 2) = 1 - μ - x
    have hn : x - 1 + μ < 0 := by linarith
    calc
      _ = |x - 1 + μ| := by simp [Real.sqrt_sq_eq_abs]
      _ = 1 - μ - x := by rw [abs_of_neg hn]; ring
  have h₀ : partialDerivative (jacobiHamiltonian μ) L 0 = 0 := by
    rw [jacobi_partial_position_one μ L hfree, hroot₁, hroot₂]
    change -x + (1 - μ) * (x + μ) / (x + μ) ^ 3 +
      μ * (x - 1 + μ) / (1 - μ - x) ^ 3 = 0
    have hratio₁ : (1 - μ) * (x + μ) / (x + μ) ^ 3 =
        (1 - μ) / (x + μ) ^ 2 := by
      have hne : x + μ ≠ 0 := ne_of_gt hr
      field_simp <;> ring
    have hratio₂ : μ * (x - 1 + μ) / (1 - μ - x) ^ 3 =
        -(μ / (1 - μ - x) ^ 2) := by
      have hne : 1 - μ - x ≠ 0 := ne_of_gt hd
      field_simp <;> ring
    rw [hratio₁, hratio₂]
    linarith [hbal]
  have h₁ : partialDerivative (jacobiHamiltonian μ) L 1 = 0 := by
    rw [jacobi_partial_position_two μ L hfree]
    simp [L]
  have h₂ : partialDerivative (jacobiHamiltonian μ) L 2 = 0 := by
    rw [jacobi_partial_momentum_one μ L hdiff]
    simp [L]
  have h₃ : partialDerivative (jacobiHamiltonian μ) L 3 = 0 := by
    rw [jacobi_partial_momentum_two μ L hdiff]
    simp [L]
  change fderiv ℝ (jacobiHamiltonian μ) L (coordinateVector 0) = 0 at h₀
  change fderiv ℝ (jacobiHamiltonian μ) L (coordinateVector 1) = 0 at h₁
  change fderiv ℝ (jacobiHamiltonian μ) L (coordinateVector 2) = 0 at h₂
  change fderiv ℝ (jacobiHamiltonian μ) L (coordinateVector 3) = 0 at h₃
  have hdecomp (w : Phase) : w =
      w 0 • coordinateVector 0 + w 1 • coordinateVector 1 +
        w 2 • coordinateVector 2 + w 3 • coordinateVector 3 := by
    funext i
    fin_cases i <;> simp [coordinateVector, Pi.add_apply, Pi.smul_apply]
  have hfd : fderiv ℝ (jacobiHamiltonian μ) L = 0 := by
    ext w
    change fderiv ℝ (jacobiHamiltonian μ) L w = 0
    rw [hdecomp w]
    simp [map_add, map_smul, h₀, h₁, h₂, h₃]
  change IsInnerLagrangePoint μ L
  refine ⟨hfree, ⟨hdiff, hfd⟩, ?_, ?_, ?_⟩
  · exact hxlo
  · exact hxhi
  · rfl

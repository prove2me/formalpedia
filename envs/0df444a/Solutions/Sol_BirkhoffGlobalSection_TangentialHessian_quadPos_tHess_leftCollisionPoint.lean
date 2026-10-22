-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.quadPos_tHess_leftCollisionPoint
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T17:40:48.281162+00:00
-- url     : https://prove2.me/submissions/935e819b-b000-49d5-a39a-57fd1cd22181

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

namespace BirkhoffGlobalSection.TangentialHessian.Sol

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian Filter Topology

noncomputable section

/-- `κ = 2c - μ² - 2μ` from the paper's Lemma 4.3. -/
def kappa (μ c : ℝ) : ℝ := 2 * c - μ ^ 2 - 2 * μ

/-- The base-point tangential Hessian divided by `w₁² = 1 - μ`. -/
def baseMat (μ c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![kappa μ c, -μ * kappa μ c, 0;
    -μ * kappa μ c, 1 + 2 * μ ^ 2 + 2 * c * μ ^ 2 - 2 * μ ^ 3, 0;
    0, 0, kappa μ c]

theorem secondCollisionDistanceSq_leftCollisionPoint (μ : ℝ) :
    secondCollisionDistanceSq (leftCollisionPoint μ) = 1 := by
  simp [secondCollisionDistanceSq, leftCollisionPoint]

theorem rD_leftCollisionPoint (μ : ℝ) : rD (leftCollisionPoint μ) = 1 := by
  simp [rD, secondCollisionDistanceSq_leftCollisionPoint]

theorem kGradR_one_leftCollisionPoint (μ c : ℝ) :
    kGradR μ c 1 (leftCollisionPoint μ) =
      ![0, -μ * Real.sqrt (1 - μ), Real.sqrt (1 - μ), 0] := by
  funext i
  fin_cases i <;> simp [kGradR, leftCollisionPoint, dP, dZ, dD, zNormSq]

theorem tHess_leftCollisionPoint (μ c : ℝ) :
    tHess μ c (leftCollisionPoint μ) =
      fun i j => Real.sqrt (1 - μ) ^ 2 * baseMat μ c i j := by
  funext i j
  simp only [tHess, tHessR, frameHess, rD_leftCollisionPoint,
    kGradR_one_leftCollisionPoint]
  fin_cases i <;> fin_cases j <;>
    simp [frame, qI, qJ, qK, Fin.sum_univ_four, kHessR,
      leftCollisionPoint, hP, hZ, dZ, dD, hD, zNormSq, baseMat, kappa] <;> ring

theorem kappa_pos {μ c : ℝ} (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2) (hc : 21 / 10 ≤ c) :
    0 < kappa μ c := by
  unfold kappa; nlinarith

/-- The base-point quadratic form is `(1-μ)(κ(x-μy)² + (1+μ²)²y² + κz²)`. -/
theorem quadForm_baseMat (μ c : ℝ) (a : Fin 3 → ℝ) :
    ∑ i, ∑ j, a i * a j * baseMat μ c i j =
      kappa μ c * (a 0 - μ * a 1) ^ 2 + (1 + μ ^ 2) ^ 2 * a 1 ^ 2
        + kappa μ c * a 2 ^ 2 := by
  simp [Fin.sum_univ_three, baseMat, kappa]
  ring

theorem quadPos_baseMat {μ c : ℝ} (hκ : 0 < kappa μ c) :
    QuadPos (baseMat μ c) := by
  intro a ha
  rw [quadForm_baseMat]
  by_contra hle
  rw [not_lt] at hle
  have t1 := mul_nonneg hκ.le (sq_nonneg (a 0 - μ * a 1))
  have t2 := mul_nonneg (sq_nonneg (1 + μ ^ 2)) (sq_nonneg (a 1))
  have t3 := mul_nonneg hκ.le (sq_nonneg (a 2))
  have e2 : (1 + μ ^ 2) ^ 2 * a 1 ^ 2 = 0 := by linarith
  have e3 : kappa μ c * a 2 ^ 2 = 0 := by linarith
  have e1 : kappa μ c * (a 0 - μ * a 1) ^ 2 = 0 := by linarith
  have h1 : a 1 = 0 := by
    rcases mul_eq_zero.mp e2 with h | h
    · nlinarith [sq_nonneg μ]
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  have h2 : a 2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    ((mul_eq_zero.mp e3).resolve_left hκ.ne')
  have h0 : a 0 = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      ((mul_eq_zero.mp e1).resolve_left hκ.ne')
    rw [h1] at this; linarith
  exact ha (funext fun i => by fin_cases i <;> simp [h0, h1, h2])

/-- Step 2b: the tangential Hessian is positive definite at the base point. -/
theorem quadPos_tHess_leftCollisionPoint {μ c : ℝ} (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc : 21 / 10 ≤ c) :
    QuadPos (tHess μ c (leftCollisionPoint μ)) := by
  intro a ha
  have hsq : 0 < Real.sqrt (1 - μ) ^ 2 := by
    have : 0 < Real.sqrt (1 - μ) := Real.sqrt_pos.mpr (by linarith)
    positivity
  have hb := quadPos_baseMat (kappa_pos hμ0 hμhalf hc) a ha
  rw [tHess_leftCollisionPoint]
  have : ∑ i, ∑ j, a i * a j * (Real.sqrt (1 - μ) ^ 2 * baseMat μ c i j) =
      Real.sqrt (1 - μ) ^ 2 * ∑ i, ∑ j, a i * a j * baseMat μ c i j := by
    simp only [Fin.sum_univ_three]; ring
  rw [this]
  exact mul_pos hsq hb

end

end BirkhoffGlobalSection.TangentialHessian.Sol

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian BirkhoffGlobalSection.TangentialHessian.Sol

theorem solution (μ c : ℝ) (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc : 21 / 10 ≤ c) :
    QuadPos (tHess μ c (leftCollisionPoint μ)) := by
  exact quadPos_tHess_leftCollisionPoint hμ0 hμhalf hc

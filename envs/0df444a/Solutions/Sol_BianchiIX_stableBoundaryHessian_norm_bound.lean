-- Prove2me | solution 1 for BianchiIX.stableBoundaryHessian_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T15:10:45.927206+00:00
-- url     : https://prove2.me/submissions/38b04ab5-f477-44df-989a-8994194ca8a3

import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_boundary_band {m c : ℝ} (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 10) :
    3 ≤ c + 1 ∧ 5 / 8 * (c + 1) ≤ m ∧ 0 ≤ m ∧ m ≤ c + 1 ∧
      0 ≤ m + 1 ∧ m + 1 ≤ 2 * (c + 1) := by
  obtain ⟨hl, hu⟩ := abs_le.mp hm
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end
end

private theorem BianchiIX.abs_five_terms (a b c d e : ℝ) :
    |a - b + c - d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have H1 := abs_sub a b
  have H2 := abs_add_le (a - b) c
  have H3 := abs_sub (a - b + c) d
  have H4 := abs_add_le (a - b + c - d) e
  linarith only [H1, H2, H3, H4]

theorem solution {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    ‖stableBoundaryHessian y v w‖ ≤ 12 * (c + 1) * ‖v‖ * ‖w‖ := by
  let K := c + 1
  let R := ‖v‖ * ‖w‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨hK, _, hm0, hmK, hm1, hm1K⟩ := stable_boundary_band hc hm
  have hKu : |y 1| ≤ K := by dsimp [K]; linarith
  have hKw : |y 2| ≤ K := by dsimp [K]; linarith
  have hKm : |y 0| ≤ K := by rwa [abs_of_nonneg hm0]
  have hKm1 : |y 0 + 1| ≤ 2 * K := by rwa [abs_of_nonneg hm1]
  have hKuw : |2 * y 1 - y 2| ≤ K := by
    have H := abs_sub (2 * y 1) (y 2)
    rw [abs_mul] at H
    norm_num only at H
    dsimp [K]
    linarith
  have hKdiff : |y 1 - y 2| ≤ K := (abs_sub _ _).trans (by dsimp [K]; linarith)
  have hp (i j : Fin 3) : |v i * w j| ≤ R := by
    rw [abs_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
      (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w j) (abs_nonneg _) (norm_nonneg _)
  have hs (i j : Fin 3) : |v i * w j + v j * w i| ≤ 2 * R :=
    (abs_add_le _ _).trans (by linarith [hp i j, hp j i])
  have ht {a A : ℝ} (ha : |a| ≤ A) (i j : Fin 3) : |a * v i * w j| ≤ A * R := by
    rw [mul_assoc, abs_mul]
    exact mul_le_mul ha (hp i j) (abs_nonneg _) ((abs_nonneg _).trans ha)
  have ht' {a A : ℝ} (ha : |a| ≤ A) (i j : Fin 3) :
      |a * (v i * w j + v j * w i)| ≤ A * (2 * R) := by
    rw [abs_mul]
    exact mul_le_mul ha (hs i j) (abs_nonneg _) ((abs_nonneg _).trans ha)
  have hscale {a A : ℝ} (ha : |a| ≤ A) {n : ℝ} (hn : 0 ≤ n) : |n * a| ≤ n * A := by
    rw [abs_mul, abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left ha hn
  have hKR : R ≤ K * R := by dsimp [K]; nlinarith
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · have H := abs_five_terms
      ((2 * y 1 - y 2) * (v 0 * w 1 + v 1 * w 0))
      (y 1 * (v 0 * w 2 + v 2 * w 0)) (2 * y 0 * v 1 * w 1)
      ((y 0 + 1) * (v 1 * w 2 + v 2 * w 1)) (2 * v 2 * w 2)
    have H1 := ht' hKuw 0 1
    have H2 := ht' hKu 0 2
    have H3 := ht (hscale hKm (by norm_num : (0 : ℝ) ≤ 2)) 1 1
    have H4 := ht' hKm1 1 2
    have H5 := ht (by norm_num : |(2 : ℝ)| ≤ 2) 2 2
    change |stableBoundaryHessian y v w 0| ≤ _ at H
    have HB : |stableBoundaryHessian y v w 0| ≤ 12 * K * R := by
      nlinarith only [H, H1, H2, H3, H4, H5, hKR, hR]
    convert! HB using 1
    dsimp [K, R]
    ring
  · have H := abs_five_terms (-y 1 * v 0 * w 0)
      (y 0 * (v 0 * w 1 + v 1 * w 0)) (3 * y 1 * v 1 * w 1)
      (y 2 * (v 1 * w 2 + v 2 * w 1)) (-y 1 * v 2 * w 2)
    have H1 := ht (by simpa only [abs_neg] using hKu : |-y 1| ≤ K) 0 0
    have H2 := ht' hKm 0 1
    have H3 := ht (hscale hKu (by norm_num : (0 : ℝ) ≤ 3)) 1 1
    have H4 := ht' hKw 1 2
    have H5 := ht (by simpa only [abs_neg] using hKu : |-y 1| ≤ K) 2 2
    have heq : -y 1 * v 0 * w 0 - y 0 * (v 0 * w 1 + v 1 * w 0) +
        3 * y 1 * v 1 * w 1 - y 2 * (v 1 * w 2 + v 2 * w 1) + -y 1 * v 2 * w 2 =
        stableBoundaryHessian y v w 1 := by dsimp [stableBoundaryHessian]; ring
    rw [heq] at H
    have HB : |stableBoundaryHessian y v w 1| ≤ 12 * K * R := by
      nlinarith only [H, H1, H2, H3, H4, H5, hKR, hR]
    convert! HB using 1
    dsimp [K, R]
    ring
  · have H := abs_five_terms (-(v 0 * w 2 + v 2 * w 0))
      (-(2 * y 2 * v 1 * w 1)) (2 * (y 1 - y 2) * (v 1 * w 2 + v 2 * w 1))
      (2 * y 1 * v 2 * w 2) 0
    have H1 := hs 0 2
    have H2 := ht (hscale hKw (by norm_num : (0 : ℝ) ≤ 2)) 1 1
    have H3 := ht' (hscale hKdiff (by norm_num : (0 : ℝ) ≤ 2)) 1 2
    have H4 := ht (hscale hKu (by norm_num : (0 : ℝ) ≤ 2)) 2 2
    simp only [sub_neg_eq_add, add_zero, abs_neg, abs_zero] at H
    change |stableBoundaryHessian y v w 2| ≤ _ at H
    have HB : |stableBoundaryHessian y v w 2| ≤ 12 * K * R := by
      nlinarith only [H, H1, H2, H3, H4, hKR, hR]
    convert! HB using 1
    dsimp [K, R]
    ring

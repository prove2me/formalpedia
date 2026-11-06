-- Prove2me | solution 1 for BianchiIX.stableStrongHessianBudget_transport
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T16:24:38.052127+00:00
-- url     : https://prove2.me/submissions/b37f78fa-7fac-46e8-936e-f168bdd838ca

import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_StableProjectionRefinementData
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


theorem solution {y v w : StableState} {a b : StableState}
    {E q : ℝ} (hE : 1 ≤ E) (hq : 0 ≤ q) (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200)
    (ha : ‖a‖ ≤ E * ‖v‖) (hb : ‖b‖ ≤ E * ‖w‖)
    (ha0 : |a 0| ≤ |v 0| + 1000 * (|y 1| + |y 2|) * E * ‖v‖)
    (hb0 : |b 0| ≤ |w 0| + 1000 * (|y 1| + |y 2|) * E * ‖w‖)
    (ha1 : |a 1| ≤ (|v 1| + 200 * |y 1| * E * ‖v‖) * q)
    (hb1 : |b 1| ≤ (|w 1| + 200 * |y 1| * E * ‖w‖) * q)
    {z : StableState} (hz1 : |z 1| ≤ |y 1| * q) (hzb : |z 1| + |z 2| ≤ |y 1| + |y 2|) :
    stableStrongHessianBudget z a b ≤ 5000 * E ^ 2 * stableStrongHessianBudget y v w * q := by
  let u := |y 1|
  let B := |y 1| + |y 2|
  let V := ‖v‖
  let W := ‖w‖
  let R := u * V * W
  let T := |v 0| * |w 1| + |v 1| * |w 0|
  let S := B * (|v 1| * W + V * |w 1|)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hB1 : B ≤ 1 / 100 := by dsimp [B]; linarith
  have hE0 : 0 ≤ E := by linarith
  have hE2 : E ≤ E ^ 2 := by nlinarith
  have hE21 : 1 ≤ E ^ 2 := by nlinarith
  have hR : 0 ≤ R := by dsimp [R, u, V, W]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hS : 0 ≤ S := by dsimp [S, B, V, W]; positivity
  have hcent : |v 0| * W + V * |w 0| ≤ 2 * V * W := by
    have Hv : |v 0| ≤ V := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 0
    have Hw : |w 0| ≤ W := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w 0
    nlinarith only [mul_le_mul_of_nonneg_right Hv (norm_nonneg w),
      mul_le_mul_of_nonneg_left Hw (norm_nonneg v)]
  have HC := mul_le_mul_of_nonneg_left hcent (show 0 ≤ 200 * u * E by dsimp [u]; positivity)
  have HR := mul_le_mul_of_nonneg_right hB1 (show 0 ≤ 400400 * E ^ 2 * R by positivity)
  have HE := mul_le_mul_of_nonneg_right hE2 hR
  have HT := mul_le_mul_of_nonneg_right hE21 hT
  have HS := mul_le_mul_of_nonneg_right hE2 hS
  have hpoly : u * E ^ 2 * V * W +
      (|v 0| + 1000 * B * E * V) * (|w 1| + 200 * u * E * W) +
      (|v 1| + 200 * u * E * V) * (|w 0| + 1000 * B * E * W) +
      B * ((|v 1| + 200 * u * E * V) * E * W + E * V * (|w 1| + 200 * u * E * W)) ≤
        5000 * E ^ 2 * (R + T + S) := by
    have heq : u * E ^ 2 * V * W +
        (|v 0| + 1000 * B * E * V) * (|w 1| + 200 * u * E * W) +
        (|v 1| + 200 * u * E * V) * (|w 0| + 1000 * B * E * W) +
        B * ((|v 1| + 200 * u * E * V) * E * W + E * V * (|w 1| + 200 * u * E * W)) =
      E ^ 2 * R + T + 1001 * E * S + 200 * u * E * (|v 0| * W + V * |w 0|) +
        400400 * B * E ^ 2 * R := by dsimp [R, T, S]; ring
    rw [heq]
    have HC' : 200 * u * E * (|v 0| * W + V * |w 0|) ≤ 400 * E * R := by
      convert! HC using 1
      dsimp [R]
      ring
    nlinarith only [HC', HR, HE, HT, HS, mul_nonneg (sq_nonneg E) hR,
      mul_nonneg (sq_nonneg E) hT, mul_nonneg (sq_nonneg E) hS]
  have H0 := mul_le_mul (mul_le_mul hz1 ha (norm_nonneg _) (by positivity)) hb (norm_nonneg _) (by positivity)
  have H1 := mul_le_mul ha0 hb1 (abs_nonneg _) (by positivity)
  have H2 := mul_le_mul ha1 hb0 (abs_nonneg _) (by positivity)
  have H3 := mul_le_mul hzb
    (add_le_add (mul_le_mul ha1 hb (norm_nonneg _) (by positivity))
      (mul_le_mul ha hb1 (abs_nonneg _) (by positivity))) (by positivity) (by positivity)
  have HP := mul_le_mul_of_nonneg_right hpoly hq
  dsimp [stableStrongHessianBudget, R, T, S, u, B, V, W] at HP ⊢
  nlinarith only [H0, H1, H2, H3, HP]

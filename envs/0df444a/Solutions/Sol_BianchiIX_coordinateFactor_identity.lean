-- Prove2me | solution 1 for BianchiIX.coordinateFactor_identity
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:07:12.608227+00:00
-- url     : https://prove2.me/submissions/6789dad7-4682-4ee3-82ef-273d286e4106

import Definitions.Def_BianchiIX_Analysis_CoordinateFactor
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.hasDerivAt_coordinateSegment {n : ℕ} (i : Fin n) (Y : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (coordinateSegment i Y) (Y i • Pi.single i 1) s := by
  convert! (hasDerivAt_update Y i (s * Y i)).scomp s ((hasDerivAt_id s).mul_const (Y i)) using 1
  simp only [one_mul]

theorem solution {n : ℕ} {f : (Fin n → ℝ) → ℝ} {i : Fin n} {Y : Fin n → ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (coordinateSegment i Y s)) :
    f Y - f (Function.update Y i 0) = Y i * coordinateFactor f i Y := by
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => f (coordinateSegment i Y t))
        (Y i * fderiv ℝ f (coordinateSegment i Y s) (Pi.single i 1)) s := by
    convert! ((hf s hs).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_coordinateSegment i Y s) using 1
    simp only [map_smul, smul_eq_mul]
  have hc : ContinuousOn (fun s => Y i * fderiv ℝ f (coordinateSegment i Y s) (Pi.single i 1))
      (Icc (0 : ℝ) 1) := by
    intro s hs
    have H := (hf s hs).continuousAt_fderiv (by norm_num)
    exact (continuousAt_const.mul
      ((H.comp (hasDerivAt_coordinateSegment i Y s).continuousAt).clm_apply continuousAt_const)).continuousWithinAt
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs))
    (hc.intervalIntegrable_of_Icc (by norm_num))
  rw [intervalIntegral.integral_const_mul] at H
  simpa only [coordinateSegment, one_mul, Function.update_eq_self, zero_mul, coordinateFactor] using H.symm

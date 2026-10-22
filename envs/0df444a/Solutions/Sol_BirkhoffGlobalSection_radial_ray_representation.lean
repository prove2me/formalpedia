-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_ray_representation
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:39:30.037274+00:00
-- url     : https://prove2.me/submissions/f7348d3e-bb47-483b-a35c-d959a39ea116

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue


open BirkhoffGlobalSection


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution (s : Phase) (hs : s ≠ 0) :
    ∃ x ∈ unitThreeSphere, ∃ R : ℝ, 0 < R ∧ (fun i : Fin 4 => R * x i) = s := by
  let Q := zNormSq s + wNormSq s
  have hQ : 0 < Q := by
    by_contra h
    have hle : Q ≤ 0 := le_of_not_gt h
    dsimp [Q, zNormSq, wNormSq] at hle
    have hz0 : s 0 = 0 := by
      nlinarith [sq_nonneg (s 0), sq_nonneg (s 1), sq_nonneg (s 2), sq_nonneg (s 3)]
    have hz1 : s 1 = 0 := by
      nlinarith [sq_nonneg (s 0), sq_nonneg (s 1), sq_nonneg (s 2), sq_nonneg (s 3)]
    have hz2 : s 2 = 0 := by
      nlinarith [sq_nonneg (s 0), sq_nonneg (s 1), sq_nonneg (s 2), sq_nonneg (s 3)]
    have hz3 : s 3 = 0 := by
      nlinarith [sq_nonneg (s 0), sq_nonneg (s 1), sq_nonneg (s 2), sq_nonneg (s 3)]
    have hz : s = 0 := by
      ext i
      change s i = 0
      fin_cases i
      · exact hz0
      · exact hz1
      · exact hz2
      · exact hz3
    exact hs hz
  let R := Real.sqrt Q
  have hR : 0 < R := Real.sqrt_pos.mpr hQ
  have hRsq : R ^ 2 = Q := Real.sq_sqrt hQ.le
  let x : Phase := R⁻¹ • s
  have hscale (a : ℝ) : zNormSq (a • s) + wNormSq (a • s) = a ^ 2 * Q := by
    simp only [zNormSq, wNormSq, Pi.smul_apply, smul_eq_mul, Q]
    ring
  refine ⟨x, ?_, R, hR, ?_⟩
  · change zNormSq (R⁻¹ • s) + wNormSq (R⁻¹ • s) = 1
    rw [hscale, ← hRsq, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hR.ne')]
  · change R • (R⁻¹ • s) = s
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]

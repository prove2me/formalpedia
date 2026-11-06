-- Prove2me | solution 1 for BianchiIX.coreAuxiliary_coefficient_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:06:35.593405+00:00
-- url     : https://prove2.me/submissions/ae8f794b-67d7-4777-a4d1-3a643922c239

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreAuxiliary
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_core_small_clock_derivatives
import Theorems.Thm_BianchiIX_core_small_coupling
import Theorems.Thm_BianchiIX_core_small_coupling_derivatives
import Theorems.Thm_BianchiIX_core_small_numerators
import Theorems.Thm_BianchiIX_core_small_radius_derivatives
import Theorems.Thm_BianchiIX_core_small_strong_derivatives
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
open BianchiIX


theorem solution {k z : ℝ} {y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 99 / 100 * k ≤ y 0 ∧ y 0 ≤ 101 / 100 * k)
    (hv : 1 ≤ y 0 / Real.cosh z)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    let r := y 0
    let v := r / Real.cosh z
    let m := (1 / 10000) / k
    let q := coreAuxiliary z y
    let h := coreAuxiliaryJacobian z y
    (0 ≤ q 0 ∧ q 0 ≤ 1 / 100) ∧ |q 2| ≤ r ∧ |q 3| ≤ 2 * r * m ∧
    999 / 1000 ≤ q 1 ∧
    |h 0 0| ≤ y 1 ∧ |h 0 1| ≤ 2 * r ∧
    |h 1 0| ≤ m / r ^ 2 ∧ |h 1 1| ≤ 2 * m / r ^ 2 ∧ |h 1 2| ≤ 2 * m / (v * r ^ 2) ∧
    |h 2 0| ≤ 3 / 4 ∧ |h 2 2| ≤ 1 / r ∧
    |h 3 0| ≤ 2 * m ∧ |h 3 1 + v| ≤ 3 * m ∧ |h 3 2| ≤ 2 * m / v := by
  let r := y 0
  let u := y 1
  let v := r / Real.cosh z
  let w := y 2 / v
  let m := (1 / 10000) / k
  let s := 1 / Real.cosh z
  let c := -Real.tanh z
  have hk0 : 0 < k := by linarith
  have hr5 : 5 ≤ r := by dsimp [r]; linarith [hr.1]
  have hr0 : 0 < r := by linarith
  have hm : 0 ≤ m ∧ m ≤ 1 / 100 := by
    dsimp [m]
    exact ⟨by positivity, (div_le_iff₀ hk0).mpr (by linarith)⟩
  have hrm : r * m ≤ 1 / 1000 := by
    dsimp [m]
    rw [← mul_div_assoc, div_le_iff₀ hk0]
    dsimp [r]
    linarith [hr.2]
  have hv' : 1 ≤ v ∧ v ≤ r := ⟨hv, div_le_self hr0.le (Real.one_le_cosh z)⟩
  have hs : 0 ≤ s ∧ s ≤ 1 :=
    ⟨by dsimp [s]; positivity, (div_le_one (Real.cosh_pos z)).mpr (Real.one_le_cosh z)⟩
  have hc : |c| ≤ 1 := by
    dsimp [c]
    rw [abs_neg]
    exact abs_le.mpr ⟨(Real.neg_one_lt_tanh z).le, (Real.tanh_lt_one z).le⟩
  obtain ⟨hC0, _, hC⟩ := core_small_coupling hm hrm hu hw hv'
  obtain ⟨ha, hg⟩ := core_small_numerators hr5 hm hrm hu hw hv' hs hc
  obtain ⟨hCR, hCU⟩ := core_small_coupling_derivatives hr5 hm hu hw hv' hs
  obtain ⟨hdR, hdU, hdP⟩ := core_small_clock_derivatives (v := v) hr5 hm hu hw (by linarith [hv'.1])
  obtain ⟨haR, haP⟩ := core_small_strong_derivatives hr5 hm hu hw hv'.1 hs
  obtain ⟨hgR, hgU, hgP⟩ := core_small_radius_derivatives hr5 hm hu hw hv' hs hc
  refine ⟨⟨hC0, hC⟩, ?_, ?_, (coreBootstrap_clock_bounds hk hr.1 hu hw).1,
    hCR, hCU, hdR, hdU, hdP, haR, haP, hgR, hgU, hgP⟩
  · convert! ha using 1
    dsimp [coreAuxiliary, r, v, w, s, c]
    congr 1
    ring
  · convert! hg using 1
    dsimp [coreAuxiliary, r, v, w, c]
    congr 1
    ring

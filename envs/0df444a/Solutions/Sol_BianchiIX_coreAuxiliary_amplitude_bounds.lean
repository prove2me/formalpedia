-- Prove2me | solution 1 for BianchiIX.coreAuxiliary_amplitude_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:31:13.008669+00:00
-- url     : https://prove2.me/submissions/3686754e-2b7b-40d1-808c-424e8642907d

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreAuxiliary
import Theorems.Thm_BianchiIX_coreAuxiliary_coefficient_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_coefficient_scales
import Theorems.Thm_BianchiIX_core_amplitude_clock_products
import Theorems.Thm_BianchiIX_core_amplitude_radius_numerators
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
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open BianchiIX


theorem solution {k z : ℝ} {y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 99 / 100 * k ≤ y 0 ∧ y 0 ≤ 101 / 100 * k)
    (hv : 1 ≤ y 0 / Real.cosh z)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    let r := y 0
    let v := r / Real.cosh z
    let w := y 2 / v
    let q := coreAuxiliary z y
    let h := coreAuxiliaryJacobian z y
    |h 3 0| ≤ 2 * y 1 + 3 * w ^ 2 / r ^ 2 ∧
    |h 3 1 + v - v * (1 - q 1)| ≤ 4 * (y 1 + w) ∧
    |v * h 3 2| ≤ 2 * (y 1 + w / r) ∧
    |q 3 * h 1 0| ≤ (y 1 + w ^ 2 / r ^ 2) / 10 ∧
    |q 3 * h 1 1| ≤ (y 1 + w / r) / 10 ∧
    |v * q 3 * h 1 2| ≤ (y 1 + w / r) / 10 := by
  intro r v w q h
  let m := (1 / 10000) / k
  obtain ⟨hr5, hm0, hm, _, _, _, _, _⟩ := coreBootstrap_coefficient_scales hk hr
  have hr0 : 0 < r := by dsimp [r]; linarith only [hr5]
  have hv0 : 0 < v := by dsimp [v, r]; linarith only [hv]
  have hv' : 1 ≤ v ∧ v ≤ r := ⟨hv, div_le_self hr0.le (Real.one_le_cosh z)⟩
  have hs : 0 ≤ 1 / Real.cosh z ∧ 1 / Real.cosh z ≤ 1 :=
    ⟨by positivity, (div_le_one (Real.cosh_pos z)).mpr (Real.one_le_cosh z)⟩
  have hc : |-Real.tanh z| ≤ 1 := by
    rw [abs_neg]
    exact abs_le.mpr ⟨(Real.neg_one_lt_tanh z).le, (Real.tanh_lt_one z).le⟩
  obtain ⟨hR, hU, hP⟩ := core_amplitude_radius_numerators hr5 ⟨hm0, hm⟩ hu hw hv' hs hc
  have hg : |q 3| ≤ 2 * r * m := (coreAuxiliary_coefficient_bounds hk hr hv hu hw).2.2.1
  obtain ⟨hpR, hpU⟩ := core_amplitude_clock_products hr5 ⟨hm0, hm⟩ hu hw hg
  refine ⟨hR, hU, hP, hpR, hpU, ?_⟩
  have hid : v * q 3 * h 1 2 = -(q 3 * h 1 1) := by
    change v * q 3 * (2 * (y 1 - w) / (v * r ^ 2)) = -(q 3 * (-2 * (y 1 - w) / r ^ 2))
    field_simp
  rw [hid, abs_neg]
  exact hpU

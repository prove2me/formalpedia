-- Prove2me | solution 1 for BianchiIX.exists_large_core_exit_factor
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:04:17.632222+00:00
-- url     : https://prove2.me/submissions/a99b8b68-b7bd-413d-be51-fcacd6eca700

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreExitFactor
import Theorems.Thm_BianchiIX_coreRegion_exit_factor_bounds
import Theorems.Thm_BianchiIX_exists_large_core_traversal
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
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
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_wall_bounds {k : ℝ} {y : ProjectiveState} (hy : coreRegion k y) :
    (0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k) ∧ (0 ≤ y 3 ∧ y 3 ≤ (1 / 10000) / k) := by
  have hv0 : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hw0 : 0 ≤ y 3 := (mul_nonneg_iff_of_pos_left hv0).mp hy.2.2.2.1
  exact ⟨hy.2.2.1, hw0, (le_mul_of_one_le_left hw0 hy.2.1).trans hy.2.2.2.2⟩

end
end

theorem solution {k u w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    let y : ProjectiveState := ![1 + Real.sqrt (k ^ 2 - 1), u, 1, w]
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T ∧
      projectiveOriginalFlow y 0 T 0 < 1 ∧
      0 < coreExitRadialFactor (projectiveOriginalFlow y 0 T) ∧
      coreExitRadialFactor (projectiveOriginalFlow y 0 T) ≤ 1 ∧
      |coreExitRadialFactor (projectiveOriginalFlow y 0 T) - 1| ≤ 8 * (u / k + w ^ 2 / k ^ 2) := by
  intro y
  have hk0 : 0 < k := by linarith only [hk]
  obtain ⟨T, hT, hfirst, hcore, hM, _, _, _, hU, hW, _⟩ := exists_large_core_traversal hk hu hw
  have hy : coreRegion k (projectiveOriginalFlow y 0 T) := (hcore T ⟨hT.le, le_rfl⟩).2
  obtain ⟨hpos, hle, herr⟩ := coreRegion_exit_factor_bounds hk hy hfirst.1.2 hM
  have hUle : projectiveOriginalFlow y 0 T 1 ≤ u := hU.trans
    (mul_le_of_le_one_left hu.1 (Real.exp_le_one_iff.mpr (by linarith only [hk])))
  have hWle : projectiveOriginalFlow y 0 T 3 ≤ w := hW.trans
    (mul_le_of_le_one_left hw.1 (Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))))
  have hW0 := (coreRegion_wall_bounds hy).2.1
  refine ⟨T, hT, hfirst, hM, hpos, hle, herr.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (add_le_add (div_le_div_of_nonneg_right hUle hk0.le)
      (div_le_div_of_nonneg_right ((sq_le_sq₀ hW0 hw.1).mpr hWle) (sq_nonneg k))) (by norm_num)

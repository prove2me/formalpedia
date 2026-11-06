-- Prove2me | solution 1 for BianchiIX.exists_connection_return
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T08:15:12.64767+00:00
-- url     : https://prove2.me/submissions/2a7d1d8f-c66f-4855-9317-e79ab9708762

import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ConnectionRegion
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Theorems.Thm_BianchiIX_exists_normalized_connection_return
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Real.Lemmas
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
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_denom_bound {m u v w : ℝ}
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    3 + m ^ 2 - 4 * u ≤ projectiveDenom (-m) u v w ∧ 0 < projectiveDenom (-m) u v w := by
  have H : 3 + m ^ 2 - 4 * u ≤ projectiveDenom (-m) u v w := by
    dsimp [projectiveDenom, curvature]
    nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu.1,
      mul_le_mul_of_nonneg_left hw.2 hu.1, sq_nonneg u, sq_nonneg (v - w)]
  exact ⟨H, by nlinarith only [H, hu.2, sq_nonneg m]⟩

end
end

/-- The stated entry range has an actual next-wall hit; zero strong wall is included. -/
theorem solution {μ u w : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hw : 0 < w ∧ w ≤ 1 / 10000) :
    let x := fromProjectiveState (connectionEntry μ u w)
    let β := fun t => toProjectiveState (normalizedMaxCurve x 0 t)
    ∃ T > (0 : ℝ), β T 3 = 1 ∧ ∀ t ∈ Icc 0 T,
      3 / (2 * μ ^ 2) ≤ 1 + normalizedMaxCurve x 0 t 0 ∧ connectionRegion μ (β t) := by
  intro x β
  have hμ1 : 1 ≤ μ := by linarith only [hμ]
  have hu' : 0 ≤ u ∧ u ≤ 1 / 10000 :=
    ⟨hu.1, hu.2.trans (div_le_self (by norm_num) hμ1)⟩
  have hw' : 0 < w ∧ w < 1 := ⟨hw.1, lt_of_le_of_lt hw.2 (by norm_num)⟩
  have hD : 0 < projectiveStateDenom (connectionEntry μ u w) :=
    (connection_denom_bound (m := μ) (v := 1) hu' (by norm_num) ⟨hw.1.le, hw'.2.le⟩).2
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hβ0 : β 0 = connectionEntry μ u w := by
    dsimp [β]
    rw [normalizedMaxCurve_initial]
    exact toProjectiveState_fromProjectiveState (ne_of_gt hD)
  have hA : 0 < 1 + normalizedMaxCurve x 0 0 0 := by
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  apply exists_normalized_connection_return hc hμ (le_refl 0) hA
  · change -β 0 0 = μ
    rw [hβ0]
    simp [connectionEntry]
  · change β 0 2 = 1
    rw [hβ0]
    rfl
  · change 0 ≤ β 0 1 ∧ β 0 1 ≤ 1 / 10000
    simpa only [hβ0, connectionEntry, Matrix.cons_val_one, Matrix.cons_val_zero] using hu'
  · change 0 < β 0 3 ∧ β 0 3 < 1
    simpa [hβ0, connectionEntry] using hw'

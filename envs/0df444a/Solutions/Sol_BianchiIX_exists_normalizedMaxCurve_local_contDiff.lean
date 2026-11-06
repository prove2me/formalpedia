-- Prove2me | solution 1 for BianchiIX.exists_normalizedMaxCurve_local_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:23:16.871179+00:00
-- url     : https://prove2.me/submissions/78f9ee0d-f8e8-43cb-9294-b06491054548

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Theorems.Thm_BianchiIX_contDiff_normalizedField
import Theorems.Thm_BianchiIX_exists_normalizedMaxCurve_local_derivative
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology


/-- Joint differentiability in initial state and time, on an actual local domain of the maximal flow. -/
theorem solution (x₀ : NormalizedState) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      (∀ x ∈ ball x₀ r, Ioo (t₀ - ε) (t₀ + ε) ⊆ normalizedMaxDomain x t₀) ∧
      ContDiffOn ℝ 1 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
        (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) := by
  obtain ⟨r, hr, ε, hε, J, hc, hcJ, hJ⟩ := exists_normalizedMaxCurve_local_derivative x₀ t₀
  let U := ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)
  let V : NormalizedState × ℝ → ℝ →L[ℝ] NormalizedState := fun z =>
    (ContinuousLinearMap.id ℝ ℝ).smulRight (normalizedField (normalizedMaxCurve z.1 t₀ z.2))
  have ho : IsOpen U := isOpen_ball.prod isOpen_Ioo
  have hcV : ContinuousOn V U :=
    (ContinuousLinearMap.smulRightL ℝ ℝ NormalizedState (ContinuousLinearMap.id ℝ ℝ)).continuous.comp_continuousOn
      ((contDiff_normalizedField 1).continuous.comp_continuousOn hc)
  have hd (z : NormalizedState × ℝ) (hz : z ∈ U) :
      HasStrictFDerivAt (fun w : NormalizedState × ℝ => normalizedMaxCurve w.1 t₀ w.2)
        ((J z).coprod (V z)) z := by
    apply hasStrictFDerivAt_uncurry_coprod
      (f := fun x t => normalizedMaxCurve x t₀ t)
      (f₁ := fun x t => J (x, t)) (f₂ := fun x t => V (x, t))
    · filter_upwards [ho.mem_nhds hz] with w hw
      exact ((hJ w.1 hw.1).2.2 w.2 hw.2).1
    · filter_upwards [ho.mem_nhds hz] with w hw
      exact (hasDerivAt_normalizedMaxCurve ((hJ w.1 hw.1).1 hw.2)).hasFDerivAt
    · exact hcJ.continuousAt (ho.mem_nhds hz)
    · exact hcV.continuousAt (ho.mem_nhds hz)
  refine ⟨r, hr, ε, hε, fun x hx => (hJ x hx).1, ?_⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn ho.uniqueDiffOn]
  exact ⟨by simp, fun z => (J z).coprod (V z),
    contDiffOn_zero.mpr (hcJ.continuousLinearMapCoprod hcV),
    fun z hz => (hd z hz).hasFDerivAt.hasFDerivWithinAt⟩

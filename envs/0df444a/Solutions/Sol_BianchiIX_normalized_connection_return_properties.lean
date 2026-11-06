-- Prove2me | solution 1 for BianchiIX.normalized_connection_return_properties
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T08:01:20.9894+00:00
-- url     : https://prove2.me/submissions/8477779f-3ddb-4920-8e66-dfc6bd02fdd6

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Definitions.Def_BianchiIX_Dynamics_ConnectionRegion
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_connection_monotonicity
import Theorems.Thm_BianchiIX_unique_crossing_of_opposite_monotonicity
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
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_coupling_bounds {u v w : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    -u ^ 2 ≤ coupling u v w ∧ coupling u v w ≤ 2 * u := by
  unfold coupling
  constructor
  · nlinarith only [mul_nonneg hu hv.1, mul_nonneg hu hw.1]
  · nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu,
      mul_le_mul_of_nonneg_left hw.2 hu, sq_nonneg u]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_speed_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    μ / 2 ≤ connectionSpeed m u v w ∧ connectionSpeed m u v w ≤ μ := by
  obtain ⟨hc₀, hc₁⟩ := connection_coupling_bounds hu.1 hv hw
  obtain ⟨hm₀, hm₁⟩ := abs_le.mp hm
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  unfold connectionSpeed
  constructor <;> nlinarith only [hc₀, hc₁, hm₀, hm₁, hu.2, hu2, hμ]

end
end

/-- A completed actual connection hits W = 1 for the first time and crosses V = W exactly once. -/
theorem solution {x : NormalizedState} {t₀ μ s t : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s) (hst : s < t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u);
    (∀ u ∈ Icc s t, connectionRegion μ (β u)) → β s 2 = 1 →
    (0 < β s 3 ∧ β s 3 < 1) → β t 3 = 1 →
    IsLeast {u | s < u ∧ u ∈ normalizedMaxDomain x t₀ ∧ β u 3 = 1} t ∧
      StrictAntiOn (fun u => β u 2) (Icc s t) ∧ StrictMonoOn (fun u => β u 3) (Icc s t) ∧
      (∀ u ∈ Ico s t, β u 3 < 1) ∧
      (∃! r, r ∈ Ioo s t ∧ β r 2 = β r 3) ∧
      HasDerivAt (fun u => β u 3)
        ((1 + normalizedMaxCurve x t₀ t 0) * connectionClockRate (β t)) t ∧
      0 < (1 + normalizedMaxCurve x t₀ t 0) * connectionClockRate (β t) := by
  intro β hregion hV hW hhit
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst.le⟩
  have htm : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  have hv : 0 < β s 2 := by rw [hV]; norm_num
  obtain ⟨hVm, hWm⟩ := normalized_connection_monotonicity hc hμ hs hst.le hA hregion hv hW.1
  change StrictAntiOn (fun u => β u 2) (Icc s t) at hVm
  change StrictMonoOn (fun u => β u 3) (Icc s t) at hWm
  have hdom : t ∈ normalizedMaxDomain x t₀ :=
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hst.le)
  have hfirst : IsLeast {u | s < u ∧ u ∈ normalizedMaxDomain x t₀ ∧ β u 3 = 1} t := by
    refine ⟨⟨hst, hdom, hhit⟩, ?_⟩
    intro u hu
    by_contra hnot
    have hut : u < t := lt_of_not_ge hnot
    have H := hWm ⟨hu.1.le, hut.le⟩ htm hut
    change β u 3 < β t 3 at H
    rw [hu.2.2, hhit] at H
    exact lt_irrefl _ H
  have hsol (u : ℝ) (hu : u ∈ Icc s t) :
      HasDerivAt β ((1 + normalizedMaxCurve x t₀ u 0) • projectiveField (β u)) u := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hu.1)
    exact hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt (hA u hu)) H.2.1
  have hcoord (i : Fin 4) : ContinuousOn (fun u => β u i) (Icc s t) :=
    fun u hu => (hasDerivAt_pi.mp (hsol u hu) i).continuousAt.continuousWithinAt
  have hcross := unique_crossing_of_opposite_monotonicity hst (hcoord 2) (hcoord 3) hVm hWm
    (by rw [hV]; exact hW.2) (by rw [hhit]; simpa only [hV] using hVm hsm htm hst)
  have hderiv := hasDerivAt_pi.mp (hsol t htm) 3
  change HasDerivAt (fun u => β u 3)
    ((1 + normalizedMaxCurve x t₀ t 0) * (connectionClockRate (β t) * β t 3)) t at hderiv
  rw [hhit, mul_one] at hderiv
  have hD : 0 < connectionClockRate (β t) := by
    have H := (connection_speed_bounds hμ (hregion t htm).1 (hregion t htm).2.1
      (hregion t htm).2.2.1 (hregion t htm).2.2.2).1
    change μ / 2 ≤ connectionClockRate (β t) at H
    linarith only [H, hμ]
  refine ⟨hfirst, hVm, hWm, ?_, hcross, hderiv, mul_pos (hA t htm) hD⟩
  intro u hu
  simpa only [hhit] using hWm ⟨hu.1, hu.2.le⟩ htm hu.2

-- Prove2me | solution 1 for BianchiIX.scaled_connection_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:48:29.70157+00:00
-- url     : https://prove2.me/submissions/a8d321dc-1387-42e7-ac2c-ec28d9a34dbd

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Definitions.Def_BianchiIX_Dynamics_ConnectionRegion
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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_active_rate_neg {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    -m - 1 - coupling u v w < 0 := by
  have H := (connection_coupling_bounds hu.1 hv hw).1
  have hu2 := pow_le_pow_left₀ hu.1 hu.2 2
  nlinarith only [H, hu2, (abs_le.mp hm).1, hμ]

end
end

private theorem BianchiIX.connection_scaled_wall_rates {y : ProjectiveState} {μ a : ℝ}
    (hμ : 4 ≤ μ) (ha : 0 < a) (hy : connectionRegion μ y) (hv : 0 < y 2) (hw : 0 < y 3) :
    a * projectiveField y 2 < 0 ∧ 0 < a * projectiveField y 3 := by
  have hr := connection_active_rate_neg hμ hy.1 hy.2.1 hy.2.2.1 hy.2.2.2
  simp only [neg_neg] at hr
  have hD : 0 < connectionClockRate y := by
    have H := (connection_speed_bounds hμ hy.1 hy.2.1 hy.2.2.1 hy.2.2.2).1
    change μ / 2 ≤ connectionClockRate y at H
    linarith only [H, hμ]
  exact ⟨mul_neg_of_pos_of_neg ha (mul_neg_of_neg_of_pos hr hv),
    mul_pos ha (mul_pos hD hw)⟩

theorem solution {β : ℝ → ProjectiveState} {a : ℝ → ℝ}
    {I : Set ℝ} {μ : ℝ} (hI : Convex ℝ I) (hμ : 4 ≤ μ)
    (ha : ∀ u ∈ I, 0 < a u)
    (hβ : ∀ u ∈ I, HasDerivAt β (a u • projectiveField (β u)) u)
    (hy : ∀ u ∈ I, connectionRegion μ (β u))
    (hv : ∀ u ∈ I, 0 < β u 2) (hw : ∀ u ∈ I, 0 < β u 3) :
    StrictAntiOn (fun u => β u 2) I ∧ StrictMonoOn (fun u => β u 3) I := by
  have hd (i : Fin 4) (u : ℝ) (hu : u ∈ I) := hasDerivAt_pi.mp (hβ u hu) i
  constructor
  · apply strictAntiOn_of_deriv_neg hI (fun u hu => (hd 2 u hu).continuousAt.continuousWithinAt)
    intro u hu
    rw [(hd 2 u (interior_subset hu)).deriv]
    exact (connection_scaled_wall_rates hμ (ha u (interior_subset hu)) (hy u (interior_subset hu))
      (hv u (interior_subset hu)) (hw u (interior_subset hu))).1
  · apply strictMonoOn_of_deriv_pos hI (fun u hu => (hd 3 u hu).continuousAt.continuousWithinAt)
    intro u hu
    rw [(hd 3 u (interior_subset hu)).deriv]
    exact (connection_scaled_wall_rates hμ (ha u (interior_subset hu)) (hy u (interior_subset hu))
      (hv u (interior_subset hu)) (hw u (interior_subset hu))).2

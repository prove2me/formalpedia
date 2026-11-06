-- Prove2me | solution 1 for BianchiIX.normalized_connection_residence
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:57:04.359198+00:00
-- url     : https://prove2.me/submissions/7092286c-b24a-4303-9c50-bc626b87d1df

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Definitions.Def_BianchiIX_Dynamics_ConnectionRegion
import Theorems.Thm_BianchiIX_connection_denom_upper
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_projective_inverse_scale
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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_inverse_scale_lower {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    3 / μ ^ 2 ≤ 6 / projectiveDenom (-m) u v w := by
  have H := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 6)
    (connection_denom_bound hu hv hw).2 (connection_denom_upper hμ hm hu hv hw)
  convert! H using 1
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_original_clock_lower {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    1 / μ ≤ (6 / projectiveDenom (-m) u v w) * connectionSpeed m u v w := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hscale := connection_inverse_scale_lower hμ hm hu hv hw
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have H := mul_le_mul hscale hD (by positivity : 0 ≤ μ / 2)
    (div_nonneg (by norm_num) (connection_denom_bound hu hv hw).2.le)
  apply le_trans _ H
  apply (div_le_iff₀ hμ0).mpr
  field_simp
  norm_num

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_connectionLog_scaled {β : ℝ → ProjectiveState} {a t : ℝ}
    (hβ : HasDerivAt β (a • projectiveField (β t)) t) (hw : β t 3 ≠ 0) :
    HasDerivAt (fun s => Real.log (β s 3)) (a * connectionClockRate (β t)) t := by
  have H := (hasDerivAt_pi.mp hβ 3).log hw
  convert! H using 1
  change a * connectionClockRate (β t) = a * weakVelocity (β t 0) (β t 1) (β t 2) (β t 3) / β t 3
  dsimp [connectionClockRate, connectionSpeed, weakVelocity]
  field_simp

end
end

/-- A connection prefix has bounded length in normalized time, even for arbitrarily small W. -/
theorem solution {x : NormalizedState} {t₀ μ s t : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u);
    (∀ u ∈ Icc s t, connectionRegion μ (β u)) → (∀ u ∈ Icc s t, 0 < β u 3) →
    (t - s) / μ ≤ Real.log (β t 3) - Real.log (β s 3) ∧
      t - s ≤ μ * Real.log (1 / β s 3) := by
  intro β hregion hw
  have hμ0 : 0 < μ := by linarith only [hμ]
  let z := fun u => Real.log (β u 3)
  let q := fun u => (1 + normalizedMaxCurve x t₀ u 0) * connectionClockRate (β u)
  have hz (u : ℝ) (hh : u ∈ Icc s t) : HasDerivAt z (q u) u := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hh.1)
    exact hasDerivAt_connectionLog_scaled
      (hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt (hA u hh)) H.2.1) (ne_of_gt (hw u hh))
  have hq (u : ℝ) (hh : u ∈ Icc s t) : 1 / μ ≤ q u := by
    have H := connection_original_clock_lower hμ (hregion u hh).1 (hregion u hh).2.1
      (hregion u hh).2.2.1 (hregion u hh).2.2.2
    simp only [neg_neg] at H
    have hc' := (normalizedMaxCurve_forward_of_constraint hc (hs.trans hh.1)).2.1
    have heq := projective_inverse_scale (ne_of_gt (hA u hh)) hc'
    change 6 / projectiveStateDenom (β u) = 1 + normalizedMaxCurve x t₀ u 0 at heq
    change 1 / μ ≤ (6 / projectiveStateDenom (β u)) * connectionClockRate (β u) at H
    rwa [heq] at H
  have H := (convex_Icc s t).mul_sub_le_image_sub_of_le_deriv (HasDerivAt.continuousOn hz)
    (fun u hh => (hz u (interior_subset hh)).differentiableAt.differentiableWithinAt)
    (fun u hh => by rw [(hz u (interior_subset hh)).deriv]; exact hq u (interior_subset hh))
    s ⟨le_rfl, hst⟩ t ⟨hst, le_rfl⟩ hst
  have H' : (t - s) / μ ≤ z t - z s := by simpa only [one_div_mul_eq_div] using H
  refine ⟨H', ?_⟩
  have hzt : z t ≤ 0 := Real.log_nonpos (hw t ⟨hst, le_rfl⟩).le (hregion t ⟨hst, le_rfl⟩).2.2.2.2
  have hL : (t - s) / μ ≤ Real.log (1 / β s 3) := by
    rw [one_div, Real.log_inv]
    linarith only [H', hzt]
  have H'' := (div_le_iff₀ hμ0).mp hL
  nlinarith only [H'']

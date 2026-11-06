-- Prove2me | solution 1 for BianchiIX.connectionLog_ratio_antitone
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:53:42.787213+00:00
-- url     : https://prove2.me/submissions/d8153c34-1feb-4d83-ad83-17209215b528

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Theorems.Thm_BianchiIX_connectionLogField_components
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
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

noncomputable section
open BianchiIX
open Set MeasureTheory

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

private theorem BianchiIX.connection_ratio_rate_neg {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    connectionStrongRate m u v w + m + 1 + coupling u v w < 0 := by
  have hm0 : 7 / 2 ≤ m := by linarith only [(abs_le.mp hm).1, hμ]
  have hm2 := mul_nonneg (sub_nonneg.mpr hm0) (show 0 ≤ m by linarith only [hm0])
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  have hc := (connection_coupling_bounds hu.1 hv hw).2
  unfold connectionStrongRate
  nlinarith only [hm0, hm2, hu2, hc, hu.2, sq_nonneg (v - w)]

end
end

private theorem BianchiIX.hasDerivAt_connectionLog_ratio {Y : ℝ → ProjectiveState} {z : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y z)) z)
    (hD : connectionClockRate (Y z) ≠ 0) (hv : Y z 2 ≠ 0) :
    HasDerivAt (fun t => Y t 1 / Y t 2)
      ((connectionStrongRate (-Y z 0) (Y z 1) (Y z 2) (Y z 3) - Y z 0 + 1 +
        coupling (Y z 1) (Y z 2) (Y z 3)) / connectionClockRate (Y z) * (Y z 1 / Y z 2)) z := by
  have H := (hasDerivAt_pi.mp hY 1).div (hasDerivAt_pi.mp hY 2) hv
  rw [(connectionLogField_components hD).2.1, (connectionLogField_components hD).2.2.1] at H
  convert! H using 1
  field_simp
  ring

theorem solution {I : Set ℝ} (hI : Convex ℝ I)
    {Y : ℝ → ProjectiveState} {μ : ℝ} (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ I, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ I, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ I, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ I, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ I, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1) :
    AntitoneOn (fun z => Y z 1 / Y z 2) I := by
  have hD (z : ℝ) (hz : z ∈ I) : 0 < connectionClockRate (Y z) := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz)).1
    change μ / 2 ≤ connectionClockRate (Y z) at H
    linarith only [H, hμ]
  have hd (z : ℝ) (hz : z ∈ I) :=
    hasDerivAt_connectionLog_ratio (hY z hz) (ne_of_gt (hD z hz)) (ne_of_gt (hv z hz).1)
  apply antitoneOn_of_deriv_nonpos hI
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt)
  intro z hz
  rw [(hd z (interior_subset hz)).deriv]
  apply mul_nonpos_of_nonpos_of_nonneg
  · apply div_nonpos_of_nonpos_of_nonneg _ (hD z (interior_subset hz)).le
    have H := connection_ratio_rate_neg hμ (hm z (interior_subset hz)) (hu z (interior_subset hz))
      ⟨(hv z (interior_subset hz)).1.le, (hv z (interior_subset hz)).2⟩ (hw z (interior_subset hz))
    linarith only [H]
  · exact div_nonneg (hu z (interior_subset hz)).1 (hv z (interior_subset hz)).1.le

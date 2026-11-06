-- Prove2me | solution 1 for BianchiIX.connectionLog_prefix_estimates
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:56:58.797783+00:00
-- url     : https://prove2.me/submissions/8c0c1ec8-8ba6-4b67-ac8c-8fe6ba2b2484

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Theorems.Thm_BianchiIX_connectionLogField_components
import Theorems.Thm_BianchiIX_connectionLog_ratio_antitone
import Theorems.Thm_BianchiIX_connection_weak_clock_rates
import Theorems.Thm_BianchiIX_homogeneous_solution_eq_exp_integral_Icc
import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
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

private theorem BianchiIX.connection_coupling_nonneg {u v w : ℝ}
    (hu : 0 ≤ u) (hw : 0 ≤ w) (huv : u ≤ v) : 0 ≤ coupling u v w := by
  unfold coupling
  exact mul_nonneg hu (by linarith only [hw, huv])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_strong_clock_rate_le {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) (huv : u ≤ v) :
    connectionStrongRate m u v w / connectionSpeed m u v w ≤ -μ / 2 := by
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hDpos : 0 < connectionSpeed m u v w := by linarith only [hD, hμ]
  have hc := connection_coupling_nonneg hu.1 hw.1 huv
  have hm0 : 0 ≤ m := by linarith only [(abs_le.mp hm).1, hμ]
  have hprod := mul_nonneg (show 0 ≤ m - μ + 1 / 2 by linarith only [(abs_le.mp hm).1]) hm0
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  apply (div_le_iff₀ hDpos).mpr
  dsimp [connectionStrongRate, connectionSpeed]
  nlinarith only [hprod, hu2, (abs_le.mp hm).2, hμ, sq_nonneg (v - w),
    mul_nonneg (show 0 ≤ μ by linarith only [hμ]) hc]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.le_exp_of_linear_deriv_le {I : Set ℝ} (hI : Convex ℝ I)
    {f f' : ℝ → ℝ} {c s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hbound : ∀ u ∈ I, f' u ≤ c * f u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (c * (t - s)) := by
  exact le_exp_of_clock_deriv_le hI hf (fun u _ => hasDerivAt_id u)
    (fun u hu => by simpa only [mul_one] using hbound u hu) hs ht hst

end
end

private theorem BianchiIX.hasDerivAt_connectionLog_product {Y : ℝ → ProjectiveState} {z : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y z)) z) (hD : connectionClockRate (Y z) ≠ 0) :
    HasDerivAt (fun t => Y t 2 * Y t 3)
      ((-2 * (1 + coupling (Y z 1) (Y z 2) (Y z 3)) / connectionClockRate (Y z)) * (Y z 2 * Y z 3)) z := by
  have H := (hasDerivAt_pi.mp hY 2).mul (hasDerivAt_pi.mp hY 3)
  rw [(connectionLogField_components hD).2.2.1, (connectionLogField_components hD).2.2.2] at H
  convert! H using 1
  dsimp [connectionClockRate, connectionSpeed] at *
  field_simp
  ring

private theorem BianchiIX.connectionLog_growing_wall {Y : ℝ → ProjectiveState} {a b : ℝ} (hab : a ≤ b)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hD : ∀ z ∈ Icc a b, connectionClockRate (Y z) ≠ 0) :
    Y b 3 = Y a 3 * Real.exp (b - a) := by
  have H := homogeneous_solution_eq_exp_integral_Icc (r := fun _ => (1 : ℝ)) hab continuousOn_const
    (fun z hz => (hasDerivAt_pi.mp (hY z hz) 3).continuousAt.continuousWithinAt)
    (fun z hz => by
      have H := hasDerivAt_pi.mp (hY z (Ioo_subset_Icc_self hz)) 3
      rw [(connectionLogField_components (hD z (Ioo_subset_Icc_self hz))).2.2.2] at H
      simpa only [one_mul] using H)
  simpa using H

/-- Every completed connection prefix has the decay rates in (B.4); wall ordering is derived. -/
theorem solution {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1) (hentry : Y a 1 ≤ Y a 2) :
    (∀ z ∈ Icc a b, Y z 1 ≤ Y z 2) ∧
      Y b 1 ≤ Y a 1 * Real.exp (-μ * (b - a) / 2) ∧
      Y b 2 ≤ Y a 2 * Real.exp (-(1 + 2 / μ) * (b - a)) ∧
      Y b 2 * Y b 3 ≤ Y a 2 * Y a 3 * Real.exp (-2 * (b - a) / μ) ∧
      Y b 3 = Y a 3 * Real.exp (b - a) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hanti := connectionLog_ratio_antitone (convex_Icc a b) hμ hY hm hu hv hw
  have huv (z : ℝ) (hz : z ∈ Icc a b) : Y z 1 ≤ Y z 2 := by
    have H := hanti ha hz hz.1
    have H₀ : Y a 1 / Y a 2 ≤ 1 := (div_le_one (hv a ha).1).mpr hentry
    exact (div_le_one (hv z hz).1).mp (H.trans H₀)
  have hD (z : ℝ) (hz : z ∈ Icc a b) : 0 < connectionClockRate (Y z) := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz)).1
    change μ / 2 ≤ connectionClockRate (Y z) at H
    linarith only [H, hμ]
  refine ⟨huv, ?_, ?_, ?_, connectionLog_growing_wall hab hY (fun z hz => ne_of_gt (hD z hz))⟩
  · have H := le_exp_of_linear_deriv_le (convex_Icc a b) (c := -μ / 2)
      (fun z hz => hasDerivAt_pi.mp (hY z hz) 1) (fun z hz => ?_) ha hb hab
    · convert! H using 1
      congr 2
      ring
    · rw [(connectionLogField_components (ne_of_gt (hD z hz))).2.1]
      exact mul_le_mul_of_nonneg_right (connection_strong_clock_rate_le hμ (hm z hz) (hu z hz)
        ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz) (huv z hz)) (hu z hz).1
  · apply le_exp_of_linear_deriv_le (convex_Icc a b)
      (fun z hz => hasDerivAt_pi.mp (hY z hz) 2) (fun z hz => ?_) ha hb hab
    rw [(connectionLogField_components (ne_of_gt (hD z hz))).2.2.1]
    have H := (connection_weak_clock_rates hμ (hm z hz) (hu z hz)
      ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz) (huv z hz)).1
    convert! mul_le_mul_of_nonneg_right H (hv z hz).1.le using 1
    simp only [connectionClockRate, neg_neg]
  · have H := le_exp_of_linear_deriv_le (convex_Icc a b) (c := -2 / μ)
      (fun z hz => hasDerivAt_connectionLog_product (hY z hz) (ne_of_gt (hD z hz)))
      (fun z hz => mul_le_mul_of_nonneg_right
        (connection_weak_clock_rates hμ (hm z hz) (hu z hz)
          ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz) (huv z hz)).2
        (mul_nonneg (hv z hz).1.le (hw z hz).1)) ha hb hab
    convert! H using 1
    congr 2
    ring

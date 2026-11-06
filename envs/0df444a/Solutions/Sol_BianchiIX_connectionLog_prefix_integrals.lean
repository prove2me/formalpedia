-- Prove2me | solution 1 for BianchiIX.connectionLog_prefix_integrals
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T08:01:12.520979+00:00
-- url     : https://prove2.me/submissions/63fa3463-e9be-4d4e-b488-82f96fb0c5d2

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Theorems.Thm_BianchiIX_connectionLogField_components
import Theorems.Thm_BianchiIX_connectionLog_prefix_estimates
import Theorems.Thm_BianchiIX_integral_le_of_dissipation
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

private theorem BianchiIX.connection_strong_rate_le {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000) :
    connectionStrongRate m u v w ≤ -μ ^ 2 / 4 := by
  have hm0 : 7 * μ / 8 ≤ m := by linarith only [(abs_le.mp hm).1, hμ]
  have hm2 := mul_nonneg (sub_nonneg.mpr hm0)
    (show 0 ≤ m + 7 * μ / 8 by linarith only [hm0, hμ])
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  unfold connectionStrongRate
  nlinarith only [hm2, hu2, hμ, sq_nonneg (μ - 4), sq_nonneg (v - w)]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiff_connectionClockRate (n : WithTop ℕ∞) : ContDiff ℝ n connectionClockRate := by
  unfold connectionClockRate connectionSpeed coupling
  fun_prop

end
end

/-- The three finite budgets use projective time, expressed as d ell / D. -/
theorem solution {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1) (hentry : Y a 1 ≤ Y a 2) :
    (∫ z in a..b, (Y z 2) ^ 2 / connectionClockRate (Y z)) ≤ 1 / (2 * μ) ∧
      (∫ z in a..b, (Y z 3) ^ 2 / connectionClockRate (Y z)) ≤ 1 / μ ∧
      (∫ z in a..b, Y z 1 / connectionClockRate (Y z)) ≤ 4 * Y a 1 / μ ^ 2 := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hμ0 : 0 < μ := by linarith only [hμ]
  have huv := (connectionLog_prefix_estimates hab hμ hY hm hu hv hw hentry).1
  have hD (z : ℝ) (hz : z ∈ Icc a b) : 0 < connectionClockRate (Y z) := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz)).1
    change μ / 2 ≤ connectionClockRate (Y z) at H
    linarith only [H, hμ]
  have hcoord (i : Fin 4) : ContinuousOn (fun z => Y z i) (Icc a b) :=
    fun z hz => (hasDerivAt_pi.mp (hY z hz) i).continuousAt.continuousWithinAt
  have hcD : ContinuousOn (fun z => connectionClockRate (Y z)) (Icc a b) :=
    (contDiff_connectionClockRate 1).continuous.comp_continuousOn (HasDerivAt.continuousOn hY)
  have hcont (i : Fin 4) : ContinuousOn (fun z => (Y z i) ^ 2 / connectionClockRate (Y z)) (Icc a b) :=
    (hcoord i |>.pow 2).div hcD (fun z hz => ne_of_gt (hD z hz))
  refine ⟨?_, ?_, ?_⟩
  · have H := integral_le_of_dissipation hab (show 0 < 2 * μ by positivity)
      (fun z hz => (hasDerivAt_pi.mp (hY z hz) 2).pow 2) (hcont 2) (fun z hz => ?_) (sq_nonneg (Y b 2))
    · apply H.trans
      apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2 * μ)
      change (Y a 2) ^ 2 ≤ 1
      nlinarith only [(hv a ha).1, (hv a ha).2, mul_nonneg (hv a ha).1.le (sub_nonneg.mpr (hv a ha).2)]
    · rw [(connectionLogField_components (ne_of_gt (hD z hz))).2.2.1]
      have hc := connection_coupling_nonneg (hu z hz).1 (hw z hz).1 (huv z hz)
      have hm' : Y z 0 - 1 - coupling (Y z 1) (Y z 2) (Y z 3) ≤ -μ := by
        linarith only [(abs_le.mp (hm z hz)).1, hc]
      have H := mul_le_mul_of_nonneg_right hm' (sq_nonneg (Y z 2))
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (hD z hz)).mpr
      norm_num only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
      field_simp [ne_of_gt (hD z hz)]
      nlinarith only [H]
  · have H := integral_le_of_dissipation hab hμ0
      (fun z hz => ((hasDerivAt_pi.mp (hY z hz) 3).pow 2).const_sub 1)
      (hcont 3) (fun z hz => ?_)
      (show 0 ≤ 1 - (Y b 3) ^ 2 by
        nlinarith only [(hw b hb).1, (hw b hb).2,
          mul_nonneg (hw b hb).1 (sub_nonneg.mpr (hw b hb).2)])
    · apply H.trans
      apply div_le_div_of_nonneg_right _ hμ0.le
      change 1 - (Y a 3) ^ 2 ≤ 1
      linarith only [sq_nonneg (Y a 3)]
    · rw [(connectionLogField_components (ne_of_gt (hD z hz))).2.2.2]
      have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz)).1
      change μ / 2 ≤ connectionClockRate (Y z) at H
      have H' := mul_le_mul_of_nonneg_right H (sq_nonneg (Y z 3))
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (hD z hz)).mpr
      norm_num only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
      nlinarith only [H']
  · have H := integral_le_of_dissipation hab (show 0 < μ ^ 2 / 4 by positivity)
      (fun z hz => hasDerivAt_pi.mp (hY z hz) 1)
      ((hcoord 1).div hcD (fun z hz => ne_of_gt (hD z hz))) (fun z hz => ?_) (hu b hb).1
    · convert! H using 1
      ring
    · rw [(connectionLogField_components (ne_of_gt (hD z hz))).2.1]
      have H := mul_le_mul_of_nonneg_right
        (connection_strong_rate_le (v := Y z 2) (w := Y z 3) hμ (hm z hz) (hu z hz)) (hu z hz).1
      simp only [Pi.div_apply]
      convert! div_le_div_of_nonneg_right H (hD z hz).le using 1 <;> ring

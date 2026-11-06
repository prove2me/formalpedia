-- Prove2me | solution 1 for BianchiIX.core_four_integral_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:37:46.401951+00:00
-- url     : https://prove2.me/submissions/208b0442-11f1-44a8-8fdf-d289162f4b05

import Theorems.Thm_BianchiIX_integral_le_of_cosh_sq
import Theorems.Thm_BianchiIX_integral_le_of_exp_decay
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
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory


theorem solution {r u v w : ℝ → ℝ} {a b k u₀ w₀ : ℝ}
    (hab : a ≤ b) (hk : 6 ≤ k) (hu₀ : 0 ≤ u₀) (hw₀ : 0 ≤ w₀)
    (hrc : ContinuousOn r (Icc a b)) (huc : ContinuousOn u (Icc a b))
    (hvc : ContinuousOn v (Icc a b)) (hwc : ContinuousOn w (Icc a b))
    (hr : ∀ z ∈ Icc a b, 9 / 10 * k ≤ r z)
    (hu : ∀ z ∈ Icc a b, 0 ≤ u z ∧ u z ≤ u₀ * Real.exp (-k * (z - a) / 4))
    (hv : ∀ z ∈ Icc a b, 0 ≤ v z ∧ v z ≤ (11 / 10) * Real.exp (z - a))
    (hw : ∀ z ∈ Icc a b, 0 ≤ w z ∧ w z ≤ w₀ ∧ w z ≤ w₀ * Real.cosh z / r z)
    (ha : Real.cosh a ≤ 11 / 10 * k) (hb : Real.cosh b ≤ 11 / 10 * k) :
    (∫ z in a..b, u z * v z) ≤ 14 * u₀ / k ∧
    (∫ z in a..b, u z * w z) ≤ 4 * u₀ * w₀ / k ∧
    (∫ z in a..b, u z ^ 2 / r z) ≤ 3 * u₀ ^ 2 / k ^ 2 ∧
    (∫ z in a..b, w z ^ 2 / r z) ≤ 4 * w₀ ^ 2 / k := by
  have hk0 : 0 < k := by linarith
  have hlo : 0 < 9 / 10 * k := by linarith
  have hr0 (z : ℝ) (hz : z ∈ Icc a b) : 0 < r z := lt_of_lt_of_le hlo (hr z hz)
  have hri (z : ℝ) (hz : z ∈ Icc a b) : r z ≠ 0 := ne_of_gt (hr0 z hz)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have H := integral_le_of_exp_decay (f := fun z => u z * v z) (B := 11 / 10 * u₀)
      hab (show 0 < k / 12 by positivity) (by positivity) (huc.mul hvc) (fun z hz => ?_)
    · apply H.trans
      apply (le_div_iff₀ hk0).mpr
      field_simp
      nlinarith
    · calc
        u z * v z ≤ (u₀ * Real.exp (-k * (z - a) / 4)) * ((11 / 10) * Real.exp (z - a)) :=
          mul_le_mul (hu z hz).2 (hv z hz).2 (hv z hz).1 (by positivity)
        _ = (11 / 10 * u₀) * Real.exp (-k * (z - a) / 4 + (z - a)) := by rw [Real.exp_add]; ring
        _ ≤ (11 / 10 * u₀) * Real.exp (-(k / 12) * (z - a)) := by
          gcongr
          nlinarith [hz.1]
  · have H := integral_le_of_exp_decay (f := fun z => u z * w z) (B := u₀ * w₀)
      hab (show 0 < k / 4 by positivity) (mul_nonneg hu₀ hw₀) (huc.mul hwc) (fun z hz => ?_)
    · convert! H using 1
      field_simp
    · have H := mul_le_mul (hu z hz).2 (hw z hz).2.1 (hw z hz).1 (by positivity)
      convert! H using 1
      rw [show -(k / 4) * (z - a) = -k * (z - a) / 4 by ring]
      ring
  · have hcont := (huc.pow 2).div hrc hri
    have H := integral_le_of_exp_decay (f := fun z => u z ^ 2 / r z)
      (B := u₀ ^ 2 / (9 / 10 * k)) hab (show 0 < k / 2 by positivity) (by positivity) hcont (fun z hz => ?_)
    · apply H.trans
      apply (le_div_iff₀ (sq_pos_of_pos hk0)).mpr
      field_simp
      nlinarith [sq_nonneg u₀]
    · have hsq := (sq_le_sq₀ (hu z hz).1 (by positivity : 0 ≤ u₀ * Real.exp (-k * (z - a) / 4))).mpr (hu z hz).2
      calc
        u z ^ 2 / r z ≤ (u₀ * Real.exp (-k * (z - a) / 4)) ^ 2 / (9 / 10 * k) :=
          (div_le_div_of_nonneg_right hsq (hr0 z hz).le).trans
            (div_le_div_of_nonneg_left (sq_nonneg _) hlo (hr z hz))
        _ = (u₀ ^ 2 / (9 / 10 * k)) * Real.exp (-(k / 2) * (z - a)) := by
          rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
          rw [show -k * (z - a) / 4 + -k * (z - a) / 4 = -(k / 2) * (z - a) by ring]
          ring
  · have hcont := (hwc.pow 2).div hrc hri
    have H := integral_le_of_cosh_sq (f := fun z => w z ^ 2 / r z)
      (B := w₀ ^ 2 / (9 / 10 * k) ^ 3) hab (by positivity) hcont (fun z hz => ?_) ha hb
    · apply H.trans
      apply (le_div_iff₀ hk0).mpr
      field_simp
      nlinarith [sq_nonneg w₀]
    · have hsq := (sq_le_sq₀ (hw z hz).1
        (div_nonneg (mul_nonneg hw₀ (Real.cosh_pos z).le) (hr0 z hz).le)).mpr (hw z hz).2.2
      calc
        w z ^ 2 / r z ≤ (w₀ * Real.cosh z / r z) ^ 2 / r z :=
          div_le_div_of_nonneg_right hsq (hr0 z hz).le
        _ = (w₀ ^ 2 * Real.cosh z ^ 2) / r z ^ 3 := by ring
        _ ≤ (w₀ ^ 2 * Real.cosh z ^ 2) / (9 / 10 * k) ^ 3 :=
          div_le_div_of_nonneg_left (by positivity) (pow_pos hlo 3) (pow_le_pow_left₀ hlo.le (hr z hz) 3)
        _ = (w₀ ^ 2 / (9 / 10 * k) ^ 3) * Real.cosh z ^ 2 := by ring

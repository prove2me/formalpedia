-- Prove2me | solution 1 for BianchiIX.coupled_clock_variation_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T16:25:44.486768+00:00
-- url     : https://prove2.me/submissions/fc87a795-b32f-4de6-8b1e-66930d7caa31

import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Theorems.Thm_BianchiIX_abs_bounds_of_forced_derivative_feedback
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

noncomputable section
open BianchiIX
open Set MeasureTheory


/-- A scalar phase coupled to two controlled transverse components is closed by one maximum. -/
theorem solution
    {Z Z' q l : ℝ → ℝ} {f : ℝ → Fin 2 → ℝ} {c : ℝ → Fin 3 → ℝ} {s t C A B Λ : ℝ}
    (hst : s ≤ t) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hZ : ∀ r ∈ Icc s t, HasDerivAt Z (Z' r) r)
    (hl : ∀ r ∈ Icc s t, HasDerivAt l (q r) r) (hls : l s = 0)
    (hqc : ContinuousOn q (Icc s t)) (hq : ∀ r ∈ Icc s t, 0 ≤ q r)
    (hcc : ContinuousOn c (Icc s t))
    (heq : ∀ r ∈ Icc s t, Z' r = q r * (c r 0 * Z r + c r 1 * f r 0 + c r 2 * f r 1))
    (htrans : ∀ r ∈ Icc s t, |f r 0 - f s 0| + |f r 1 - f s 1| ≤
      C * (A + ∫ z in s..r, |Z z| * q z))
    (hsource : (∫ r in s..t, coupledVariationSource C A (f s 0) (f s 1) (c r) * q r) ≤ B)
    (hbudget : (∫ r in s..t, coupledVariationFeedback C (l r) (c r) * q r) ≤ Λ)
    (hΛ : Λ < 1) :
    ∀ r ∈ Icc s t,
      |Z r| ≤ (|Z s| + B) / (1 - Λ) ∧
      |Z r - Z s| ≤ B + Λ * ((|Z s| + B) / (1 - Λ)) ∧
      |f r 0 - f s 0| + |f r 1 - f s 1| ≤ C * (A + l r * ((|Z s| + B) / (1 - Λ))) := by
  let e := fun r => coupledVariationSource C A (f s 0) (f s 1) (c r) * q r
  let K := fun r => coupledVariationFeedback C (l r) (c r) * q r
  have hc (i : Fin 3) := (continuous_apply i).comp_continuousOn hcc
  have he : ContinuousOn e (Icc s t) :=
    ((((hc 1).abs.mul_const _).add ((hc 2).abs.mul_const _)).add
      (((hc 1).abs.add (hc 2).abs).const_mul (C * A))).mul hqc
  have hK : ContinuousOn K (Icc s t) :=
    (((hc 0).abs.add ((HasDerivAt.continuousOn hl).mul ((hc 1).abs.add (hc 2).abs))).const_mul (C + 1)).mul hqc
  have hclock (r : ℝ) (hr : r ∈ Icc s t) : (∫ z in s..r, q z) = l r := by
    have hsub : Icc s r ⊆ Icc s t := Icc_subset_Icc_right hr.2
    have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun z hz => hl z (hsub ((uIcc_of_le hr.1) ▸ hz)))
      ((hqc.mono hsub).intervalIntegrable_of_Icc hr.1)
    simpa only [hls, sub_zero] using H
  have hl0 (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ l r := by
    rw [← hclock r hr]
    exact intervalIntegral.integral_nonneg hr.1 (fun z hz => hq z ⟨hz.1, hz.2.trans hr.2⟩)
  have he0 (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ e r := by
    dsimp [e, coupledVariationSource]
    positivity [hq r hr]
  have hK0 (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ K r := by
    dsimp [K, coupledVariationFeedback]
    positivity [hl0 r hr, hq r hr]
  have hcap (Q : ℝ) (hbound : ∀ r ∈ Icc s t, |Z r| ≤ Q) (r : ℝ) (hr : r ∈ Icc s t) :
      |f r 0 - f s 0| + |f r 1 - f s 1| ≤ C * (A + l r * Q) := by
    have hsub : Icc s r ⊆ Icc s t := Icc_subset_Icc_right hr.2
    have HI := intervalIntegral.integral_mono_on (μ := volume) hr.1
      ((((HasDerivAt.continuousOn hZ).abs.mul hqc).mono hsub).intervalIntegrable_of_Icc hr.1)
      (((hqc.const_mul Q).mono hsub).intervalIntegrable_of_Icc hr.1)
      (fun z hz => mul_le_mul_of_nonneg_right (hbound z (hsub hz)) (hq z (hsub hz)))
    rw [intervalIntegral.integral_const_mul, hclock r hr] at HI
    simp only [Pi.mul_apply] at HI
    exact (htrans r hr).trans (mul_le_mul_of_nonneg_left (by nlinarith only [HI]) hC)
  have hfeedback (Q : ℝ) (hQ : 0 ≤ Q) (hbound : ∀ r ∈ Icc s t, |Z r| ≤ Q)
      (r : ℝ) (hr : r ∈ Icc s t) : |Z' r| ≤ e r + K r * Q := by
    let R := C * (A + l r * Q)
    have H := hcap Q hbound r hr
    have hx : |f r 0| ≤ |f s 0| + R := by
      have HT : |f r 0| ≤ |f r 0 - f s 0| + |f s 0| := by
        simpa only [sub_add_cancel] using abs_add_le (f r 0 - f s 0) (f s 0)
      linarith only [H, HT, abs_nonneg (f r 1 - f s 1)]
    have hy : |f r 1| ≤ |f s 1| + R := by
      have HT : |f r 1| ≤ |f r 1 - f s 1| + |f s 1| := by
        simpa only [sub_add_cancel] using abs_add_le (f r 1 - f s 1) (f s 1)
      linarith only [H, HT, abs_nonneg (f r 0 - f s 0)]
    have HT : |c r 0 * Z r + c r 1 * f r 0 + c r 2 * f r 1| ≤
        |c r 0| * Q + |c r 1| * (|f s 0| + R) + |c r 2| * (|f s 1| + R) := by
      calc
        _ ≤ |c r 0 * Z r| + |c r 1 * f r 0| + |c r 2 * f r 1| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ _ := by
          simp only [abs_mul]
          exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hbound r hr) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hx (abs_nonneg _))) (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
    have HB : |c r 0| * Q + |c r 1| * (|f s 0| + R) + |c r 2| * (|f s 1| + R) ≤
        coupledVariationSource C A (f s 0) (f s 1) (c r) + coupledVariationFeedback C (l r) (c r) * Q := by
      dsimp [R, coupledVariationSource, coupledVariationFeedback]
      nlinarith only [mul_nonneg (mul_nonneg hC (abs_nonneg (c r 0))) hQ,
        mul_nonneg (mul_nonneg (hl0 r hr) (add_nonneg (abs_nonneg (c r 1)) (abs_nonneg (c r 2)))) hQ]
    rw [heq r hr, abs_mul, abs_of_nonneg (hq r hr)]
    exact (mul_le_mul_of_nonneg_left (HT.trans HB) (hq r hr)).trans_eq (by dsimp [e, K]; ring)
  have H := abs_bounds_of_forced_derivative_feedback hst hZ hK hK0 he he0 hbudget hΛ hfeedback
  have hΛ0 : 0 ≤ Λ := (intervalIntegral.integral_nonneg hst hK0).trans hbudget
  have HM : (|Z s| + ∫ r in s..t, e r) / (1 - Λ) ≤ (|Z s| + B) / (1 - Λ) :=
    div_le_div_of_nonneg_right (add_le_add le_rfl hsource) (sub_pos.mpr hΛ).le
  have hbound (r : ℝ) (hr : r ∈ Icc s t) := (H r hr).1.trans HM
  intro r hr
  refine ⟨hbound r hr, ?_, hcap _ hbound r hr⟩
  have HI := (H r hr).2
  rw [mul_div_assoc] at HI
  exact HI.trans (add_le_add hsource (mul_le_mul_of_nonneg_left HM hΛ0))

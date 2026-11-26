-- Prove2me | solution 1 for CurrentChordEstimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:51:45.40783+00:00
-- url     : https://prove2.me/submissions/b32bbe57-a7a9-4dfe-9944-8f64839981b0

import Definitions.Def_Tablet_CurveCurrentBound
import Definitions.Def_Tablet_CurrentChordEstimate
import Theorems.Thm_CurveCurrentBound
import Theorems.Thm_CurveLipschitz


set_option autoImplicit false
open MeasureTheory intervalIntegral
theorem _root_.solution {E : Type*} [MetricSpace E] (σ : Curve E) (ω : Form1 E)
    (u : ℝ) (hu0 : 0 ≤ u) (huL : u ≤ σ.len) :
    |curveCurrent σ ω
        - ω.f (σ.toFun u) * (ω.pi (σ.toFun σ.len) - ω.pi (σ.toFun 0))|
      ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) * σ.len ^ 2 / 2 := by
-- BODY
  have hL : (0:ℝ) ≤ σ.len := σ.len_nonneg
  have hlip : LipschitzWith ω.piLip (ω.pi ∘ σ.toFun) := by
    have h := ω.pi_lipschitz.comp (CurveLipschitz σ)
    simpa using h
  have hcont : Continuous (ω.f ∘ σ.toFun) :=
    ω.f_lipschitz.continuous.comp (CurveLipschitz σ).continuous
  have hac : AbsolutelyContinuousOnInterval (ω.pi ∘ σ.toFun) 0 σ.len :=
    (hlip.lipschitzOnWith).absolutelyContinuousOnInterval
  have hD : IntervalIntegrable (deriv (ω.pi ∘ σ.toFun)) volume 0 σ.len :=
    hac.intervalIntegrable_deriv
  have hI1 : IntervalIntegrable
      (fun t => ω.f (σ.toFun t) * deriv (ω.pi ∘ σ.toFun) t) volume 0 σ.len := by
    have := hD.continuousOn_mul (hcont.continuousOn (s := Set.uIcc (0:ℝ) σ.len))
    simpa [Function.comp] using this
  have hI2 : IntervalIntegrable
      (fun t => ω.f (σ.toFun u) * deriv (ω.pi ∘ σ.toFun) t) volume 0 σ.len :=
    hD.const_mul _
  have hsplit : curveCurrent σ ω - ω.f (σ.toFun u) * (ω.pi (σ.toFun σ.len) - ω.pi (σ.toFun 0))
      = ∫ t in (0:ℝ)..σ.len,
          (ω.f (σ.toFun t) - ω.f (σ.toFun u)) * deriv (ω.pi ∘ σ.toFun) t := by
    have hftc : (∫ t in (0:ℝ)..σ.len, deriv (ω.pi ∘ σ.toFun) t)
        = ω.pi (σ.toFun σ.len) - ω.pi (σ.toFun 0) := by
      simpa [Function.comp] using hac.integral_deriv_eq_sub
    rw [show (fun t => (ω.f (σ.toFun t) - ω.f (σ.toFun u)) * deriv (ω.pi ∘ σ.toFun) t)
          = (fun t => ω.f (σ.toFun t) * deriv (ω.pi ∘ σ.toFun) t
              - ω.f (σ.toFun u) * deriv (ω.pi ∘ σ.toFun) t) from by funext t; ring,
      intervalIntegral.integral_sub hI1 hI2, intervalIntegral.integral_const_mul, hftc]
    rfl
  rw [hsplit]
  have hI3 : IntervalIntegrable
      (fun t => (ω.f (σ.toFun t) - ω.f (σ.toFun u)) * deriv (ω.pi ∘ σ.toFun) t)
      volume 0 σ.len := by
    have := hI1.sub hI2
    simpa [sub_mul] using this
  have hbound : ∀ t : ℝ,
      |(ω.f (σ.toFun t) - ω.f (σ.toFun u)) * deriv (ω.pi ∘ σ.toFun) t|
        ≤ ((ω.fLip : ℝ) * |t - u|) * (ω.piLip : ℝ) := by
    intro t
    have hd : |deriv (ω.pi ∘ σ.toFun) t| ≤ (ω.piLip : ℝ) := by
      by_cases h : DifferentiableAt ℝ (ω.pi ∘ σ.toFun) t
      · simpa using h.hasDerivAt.le_of_lipschitz hlip
      · simp [deriv_zero_of_not_differentiableAt h, ω.piLip.coe_nonneg]
    have hf : |ω.f (σ.toFun t) - ω.f (σ.toFun u)| ≤ (ω.fLip : ℝ) * |t - u| := by
      have h1 : dist (ω.f (σ.toFun t)) (ω.f (σ.toFun u))
          ≤ (ω.fLip : ℝ) * dist (σ.toFun t) (σ.toFun u) := by
        simpa [Real.dist_eq] using ω.f_lipschitz.dist_le_mul (σ.toFun t) (σ.toFun u)
      have h2 : dist (σ.toFun t) (σ.toFun u) ≤ |t - u| := by
        simpa [Real.dist_eq] using (CurveLipschitz σ).dist_le_mul t u
      calc |ω.f (σ.toFun t) - ω.f (σ.toFun u)| = dist (ω.f (σ.toFun t)) (ω.f (σ.toFun u)) := by
              rw [Real.dist_eq]
        _ ≤ (ω.fLip : ℝ) * dist (σ.toFun t) (σ.toFun u) := h1
        _ ≤ (ω.fLip : ℝ) * |t - u| := by
              exact mul_le_mul_of_nonneg_left h2 ω.fLip.coe_nonneg
    rw [abs_mul]
    exact mul_le_mul hf hd (abs_nonneg _) (mul_nonneg ω.fLip.coe_nonneg (abs_nonneg _))
  calc |∫ t in (0:ℝ)..σ.len, (ω.f (σ.toFun t) - ω.f (σ.toFun u)) * deriv (ω.pi ∘ σ.toFun) t|
      ≤ ∫ t in (0:ℝ)..σ.len, |(ω.f (σ.toFun t) - ω.f (σ.toFun u)) * deriv (ω.pi ∘ σ.toFun) t| :=
        intervalIntegral.abs_integral_le_integral_abs hL
    _ ≤ ∫ t in (0:ℝ)..σ.len, ((ω.fLip : ℝ) * (ω.piLip : ℝ)) * |t - u| := by
        refine intervalIntegral.integral_mono_on hL hI3.abs
          ((continuous_const.mul (continuous_id.sub continuous_const).abs).intervalIntegrable
            0 σ.len) ?_
        intro t _
        calc |(ω.f (σ.toFun t) - ω.f (σ.toFun u)) * deriv (ω.pi ∘ σ.toFun) t|
            ≤ ((ω.fLip : ℝ) * |t - u|) * (ω.piLip : ℝ) := hbound t
          _ = ((ω.fLip : ℝ) * (ω.piLip : ℝ)) * |t - u| := by ring
    _ ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) * σ.len ^ 2 / 2 := by
        rw [intervalIntegral.integral_const_mul]
        have hnn : (0:ℝ) ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) :=
          mul_nonneg ω.fLip.coe_nonneg ω.piLip.coe_nonneg
        have habsint : (∫ t in (0:ℝ)..σ.len, |t - u|) = (u ^ 2 + (σ.len - u) ^ 2) / 2 := by
          have h1 : (∫ t in (0:ℝ)..u, |t - u|) = ∫ t in (0:ℝ)..u, (u - t) := by
            refine intervalIntegral.integral_congr ?_
            intro t ht
            rw [Set.uIcc_of_le hu0] at ht
            show |t - u| = u - t
            rw [abs_of_nonpos (by linarith [ht.2])]
            ring
          have h2 : (∫ t in u..σ.len, |t - u|) = ∫ t in u..σ.len, (t - u) := by
            refine intervalIntegral.integral_congr ?_
            intro t ht
            rw [Set.uIcc_of_le huL] at ht
            show |t - u| = t - u
            rw [abs_of_nonneg (by linarith [ht.1])]
          have hadd : (∫ t in (0:ℝ)..u, |t - u|) + (∫ t in u..σ.len, |t - u|)
              = ∫ t in (0:ℝ)..σ.len, |t - u| := by
            refine intervalIntegral.integral_add_adjacent_intervals ?_ ?_ <;>
              exact (Continuous.intervalIntegrable (by continuity) _ _)
          rw [← hadd, h1, h2]
          have e1 : (∫ t in (0:ℝ)..u, (u - t)) = u ^ 2 / 2 := by
            have := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := u) (fun x : ℝ => x) u
            simpa [integral_id] using this
          have e2 : (∫ t in u..σ.len, (t - u)) = (σ.len - u) ^ 2 / 2 := by
            have := intervalIntegral.integral_comp_sub_right (a := u) (b := σ.len) (fun x : ℝ => x) u
            simpa [integral_id] using this
          rw [e1, e2]; ring
        rw [habsint]
        have hsq : u ^ 2 + (σ.len - u) ^ 2 ≤ σ.len ^ 2 := by
          nlinarith [mul_nonneg hu0 (sub_nonneg.mpr huL)]
        have := mul_le_mul_of_nonneg_left hsq hnn
        linarith [this]

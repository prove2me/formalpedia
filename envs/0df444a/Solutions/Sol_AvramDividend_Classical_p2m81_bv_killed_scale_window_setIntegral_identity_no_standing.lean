-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_killed_scale_window_setIntegral_identity_no_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T08:08:14.726511+00:00
-- url     : https://prove2.me/submissions/17c7bcd2-055b-452a-87aa-6db551bf565a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_shifted_expectation_of_scalar_renewal_kernel
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation) (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) (T : ℝ≥0)
    (τ : ℕ → ℝ≥0) (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ, ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T) (hT : s + T = u) (hTc : (T : ℝ) = (u : ℝ) - (s : ℝ))
    (hEvent : ∀ ω : Ω, (∀ v : ℝ≥0, v ≤ T →
      0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)) ↔ ω ∈
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)})
    (hf : Integrable (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω))) P)
    (hg : Integrable (fun ω => W (x + X.X s ω)) P)
    (hf0 : ∀ ω : Ω, 0 ≤ (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω))) ω)
    (hg0 : ∀ ω : Ω, 0 ≤ W (x + X.X s ω))
    (hScalar : ∀ h : ℝ,
      (∫⁻ z : ℝ≥0 → ℝ,
        if ∀ j : ℕ, τ j ≤ T → 0 ≤ h + z (τ j) then
          ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W (h + z T))
        else (0 : ℝ≥0∞)
        ∂(Measure.map (fun ω : Ω => (fun t : ℝ≥0 => X.X t ω)) P)) =
      ENNReal.ofReal (W h))
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫ ω, A.indicator (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω))) ω ∂P) =
    ∫ ω, A.indicator (fun ω => W (x + X.X s ω)) ω ∂P := by
  classical
  let E : Set Ω := {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u → 0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}
  let f : Ω → ℝ := E.indicator (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) * W (x + X.X u ω))
  let g : Ω → ℝ := fun ω => W (x + X.X s ω)
  have hWmeas : Measurable W := (scaleFunction_monotone X q W hW).measurable
  have hAΩ : MeasurableSet A := (𝓕.le s) A hA
  let H : Ω → ℝ := fun ω => if ω ∈ A then x + X.X s ω else -1
  have hH : Measurable[𝓕 s] H := Measurable.ite hA (measurable_const.add (X.adapted s)) measurable_const
  have hKernel := chat04_killed_scale_shifted_expectation_of_scalar_renewal_kernel X s H hH τ T hCover hTerminal q W hW hScalar
  have hLeft (ω : Ω) : (if ∀ v : ℝ≥0, v ≤ T → 0 ≤ H ω + (X.X (s + v) ω - X.X s ω) then ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W (H ω + (X.X (s + T) ω - X.X s ω))) else (0 : ℝ≥0∞)) = ENNReal.ofReal (A.indicator f ω) := by
    by_cases ha : ω ∈ A
    · by_cases he : ω ∈ E
      · have hs : ∀ v : ℝ≥0, v ≤ T → 0 ≤ H ω + (X.X (s + v) ω - X.X s ω) := by simpa only [H, if_pos ha] using (hEvent ω).mpr he
        have hPay : Real.exp (-(q * (T : ℝ))) * W (H ω + (X.X (s + T) ω - X.X s ω)) = f ω := by simp only [H, if_pos ha, f, Set.indicator_of_mem he, hT, hTc]; congr 1; ring
        simpa only [if_pos hs, Set.indicator_of_mem ha, hPay]
      · have hs : ¬ (∀ v : ℝ≥0, v ≤ T → 0 ≤ H ω + (X.X (s + v) ω - X.X s ω)) := fun hh => he ((hEvent ω).mp (by simpa only [H, if_pos ha] using hh))
        have hPay : A.indicator f ω = 0 := by simp only [Set.indicator_of_mem ha, f, Set.indicator_of_notMem he]
        simpa only [if_neg hs, hPay, ENNReal.ofReal_zero]
    · have hs : ¬ (∀ v : ℝ≥0, v ≤ T → 0 ≤ H ω + (X.X (s + v) ω - X.X s ω)) := by intro hh; have hz := hh 0 (show (0 : ℝ≥0) ≤ T from zero_le); norm_num [H, ha, X.X_zero ω] at hz
      have hPay : A.indicator f ω = 0 := Set.indicator_of_notMem ha _
      simpa only [if_neg hs, hPay, ENNReal.ofReal_zero]
  have hRight : (∫⁻ y, ENNReal.ofReal (W y) ∂(Measure.map H P)) = ∫⁻ ω, ENNReal.ofReal (A.indicator g ω) ∂P := by
    have hHΩ : Measurable H := hH.mono (𝓕.le s) le_rfl
    refine (lintegral_map (ENNReal.measurable_ofReal.comp hWmeas) hHΩ).trans (lintegral_congr fun ω => ?_)
    by_cases ha : ω ∈ A
    · simp [H, g, ha, Set.indicator]
    · have hWneg : W (-1) = 0 := hW.1 (-1) (by norm_num)
      simp [H, g, ha, hWneg, Set.indicator]
  have hMasked : (∫⁻ ω, ENNReal.ofReal (A.indicator f ω) ∂P) = ∫⁻ ω, ENNReal.ofReal (A.indicator g ω) ∂P := ((lintegral_congr hLeft).symm.trans hKernel).trans hRight
  have hfA : Integrable (A.indicator f) P := hf.indicator hAΩ
  have hgA : Integrable (A.indicator g) P := hg.indicator hAΩ
  have hfA0 : 0 ≤ᵐ[P] A.indicator f := ae_of_all P fun ω => by
    by_cases ha : ω ∈ A
    · simpa [E, f, Set.indicator, ha] using hf0 ω
    · simp [Set.indicator, ha]
  have hgA0 : 0 ≤ᵐ[P] A.indicator g := ae_of_all P fun ω => by
    by_cases ha : ω ∈ A
    · simpa [g, Set.indicator, ha] using hg0 ω
    · simp [Set.indicator, ha]
  have hReal : (∫ ω, A.indicator f ω ∂P) = ∫ ω, A.indicator g ω ∂P := by
    have h : ENNReal.ofReal (∫ ω, A.indicator f ω ∂P) = ENNReal.ofReal (∫ ω, A.indicator g ω ∂P) := by rw [ofReal_integral_eq_lintegral_ofReal hfA hfA0, ofReal_integral_eq_lintegral_ofReal hgA hgA0]; exact hMasked
    have h2 := congrArg ENNReal.toReal h
    simpa only [ENNReal.toReal_ofReal (integral_nonneg_of_ae hfA0), ENNReal.toReal_ofReal (integral_nonneg_of_ae hgA0)] using h2
  exact hReal

-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_future_window_killed_scale_harmonicity_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T07:59:08.289082+00:00
-- url     : https://prove2.me/submissions/6a0df2e3-3ac6-4033-8417-489b09be3b35

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_future_window_killed_scale_integrable_no_standing
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_fixedTime_scale_integrable_of_root_no_standing
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule
import Theorems.Thm_AvramDividend_Classical_chat04_lower_killing_future_window_reindex
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_path_killed_scale_scalar_no_standing_public
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_killed_scale_window_setIntegral_identity_no_standing

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω)) | 𝓕 s] =ᵐ[P]
      (fun ω => W (x + X.X s ω)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let T : ℝ≥0 := u - s
  let E : Set Ω := {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u → 0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}
  let f : Ω → ℝ := E.indicator (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) * W (x + X.X u ω))
  let g : Ω → ℝ := fun ω => W (x + X.X s ω)
  have hf : Integrable f P := p2m81_bv_future_window_killed_scale_integrable_no_standing X q φ hq hφ hroot W hW x s u hsu
  have hg : Integrable g P := p2m81_bv_fixedTime_scale_integrable_of_root_no_standing X q φ hq hφ hroot W hW x s
  have hW0 (y : ℝ) : 0 ≤ W y := by
    by_cases hy : 0 ≤ y
    · exact hW.2.1 y hy
    · simpa only [hW.1 y (lt_of_not_ge hy)] using (le_refl (0 : ℝ))
  have hf0 (ω : Ω) : 0 ≤ f ω := by
    by_cases he : ω ∈ E
    · simp only [f, Set.indicator, if_pos he]
      exact mul_nonneg (Real.exp_nonneg _) (hW0 _)
    · simp only [f, Set.indicator, if_neg he]
      exact le_refl 0
  have hg0 (ω : Ω) : 0 ≤ g ω := hW0 _
  have hWmeas : Measurable W := (scaleFunction_monotone X q W hW).measurable
  have hgm : Measurable[𝓕 s] g := hWmeas.comp (measurable_const.add (X.adapted s))
  have hT : s + T = u := by simpa only [T] using add_tsub_cancel_of_le hsu
  have hTc : (T : ℝ) = (u : ℝ) - (s : ℝ) := by simpa only [T] using (NNReal.coe_sub hsu)
  have hWindow : E = {ω : Ω | ∀ v : ℝ≥0, v ≤ T → 0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)} := chat04_lower_killing_future_window_reindex X x s u hsu
  have hEvent (ω : Ω) : (∀ v : ℝ≥0, v ≤ T → 0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)) ↔ ω ∈ E := (Set.ext_iff.mp hWindow ω).symm
  obtain ⟨τ, hCover, hTerminal⟩ := chat04_explicit_shifted_killed_survival_schedule T
  have hScalar : ∀ h : ℝ, (∫⁻ z : ℝ≥0 → ℝ, if ∀ j : ℕ, τ j ≤ T → 0 ≤ h + z (τ j) then ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W (h + z T)) else (0 : ℝ≥0∞) ∂(Measure.map (fun ω : Ω => (fun t : ℝ≥0 => X.X t ω)) P)) = ENNReal.ofReal (W h) := fun h => p2m81_bv_path_killed_scale_scalar_no_standing_public X q φ hq hφ hroot W hW hBV h T τ hCover hTerminal
  refine (ae_eq_condExp_of_forall_setIntegral_eq (m := 𝓕 s) (m₀ := mΩ) (μ := P) (𝓕.le s) hf ?_ ?_ hgm.aestronglyMeasurable).symm
  · intro A _ _
    exact hg.integrableOn
  · intro A hA _
    have hAΩ : MeasurableSet A := (𝓕.le s) A hA
    have hId := p2m81_bv_killed_scale_window_setIntegral_identity_no_standing X q φ hq hφ hroot W hW hBV x s u hsu T τ hCover hTerminal hT hTc hEvent hf hg hf0 hg0 hScalar A hA
    simpa only [integral_indicator hAΩ] using hId.symm

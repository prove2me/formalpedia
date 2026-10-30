-- Prove2me | solution 1 for AvramDividend.Classical.boundedVariation_future_window_killed_scale_harmonicity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:38:33.050093+00:00
-- url     : https://prove2.me/submissions/fdccdf7c-639e-42d2-88e2-51088fe50fba

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_original_path_killed_scale_scalar
import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_shifted_expectation_of_scalar_renewal_kernel
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule
import Theorems.Thm_AvramDividend_Classical_chat04_lower_killing_future_window_reindex
import Theorems.Thm_AvramDividend_Classical_chat04_standing_future_window_killed_scale_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_standing_scale_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
/-- BV source-killed semigroup and Lévy restart identify the future payoff conditionally. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω)) | 𝓕 s] =ᵐ[P]
      (fun ω => W (x + X.X s ω)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let T : ℝ≥0 := u - s
  let E : Set Ω := {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u → 0 ≤
    (x + X.X s ω) + (X.X v ω - X.X s ω)}
  let f : Ω → ℝ := E.indicator (fun ω => Real.exp
    (-(q * ((u : ℝ) - (s : ℝ)))) * W (x + X.X u ω))
  let g : Ω → ℝ := fun ω => W (x + X.X s ω)
  have hf : Integrable f P := chat04_standing_future_window_killed_scale_integrable X hX q hq W hW x s u hsu
  have hg : Integrable g P := chat04_standing_scale_fixed_time_integrable X hX q hq W hW x s
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
  have hgm : Measurable[𝓕 s] g :=
    hWmeas.comp (measurable_const.add (X.adapted s))
  have hT : s + T = u := by simpa only [T] using add_tsub_cancel_of_le hsu
  have hTc : (T : ℝ) = (u : ℝ) - (s : ℝ) := by simpa only [T] using (NNReal.coe_sub hsu)
  have hWindow : E = {ω : Ω | ∀ v : ℝ≥0, v ≤ T →
      0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)} := chat04_lower_killing_future_window_reindex X x s u hsu
  have hEvent (ω : Ω) : (∀ v : ℝ≥0, v ≤ T →
      0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)) ↔ ω ∈ E := (Set.ext_iff.mp hWindow ω).symm
  obtain ⟨τ, hCover, hTerminal⟩ := chat04_explicit_shifted_killed_survival_schedule T
  refine (ae_eq_condExp_of_forall_setIntegral_eq
    (m := 𝓕 s) (m₀ := mΩ) (μ := P)
    (𝓕.le s) hf ?_ ?_ hgm.aestronglyMeasurable).symm
  · intro A _ _
    exact hg.integrableOn
  · intro A hA _
    have hAΩ : MeasurableSet A := (𝓕.le s) A hA
    let H : Ω → ℝ := fun ω => if ω ∈ A then x + X.X s ω else -1
    have hH : Measurable[𝓕 s] H := Measurable.ite hA (measurable_const.add (X.adapted s)) measurable_const
    have hScalar (y : ℝ) := avram_ws01b_bv_original_path_killed_scale_scalar X hX q hq W hW hBV y T τ hCover hTerminal
    have hKernel := chat04_killed_scale_shifted_expectation_of_scalar_renewal_kernel X s H hH τ T hCover hTerminal q W hW hScalar
    have hLeft (ω : Ω) :
        (if ∀ v : ℝ≥0, v ≤ T → 0 ≤ H ω + (X.X (s + v) ω - X.X s ω)
          then ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) *
            W (H ω + (X.X (s + T) ω - X.X s ω))) else (0 : ℝ≥0∞)) =
        ENNReal.ofReal (A.indicator f ω) := by
      by_cases ha : ω ∈ A
      · by_cases he : ω ∈ E
        · have hs : ∀ v : ℝ≥0, v ≤ T →
            0 ≤ H ω + (X.X (s + v) ω - X.X s ω) := by
              simpa only [H, if_pos ha] using (hEvent ω).mpr he
          have hPay : Real.exp (-(q * (T : ℝ))) *
              W (H ω + (X.X (s + T) ω - X.X s ω)) = f ω := by
            simp only [H, if_pos ha, f, Set.indicator_of_mem he, hT, hTc]
            congr 1
            ring
          simpa only [if_pos hs, Set.indicator_of_mem ha, hPay]
        · have hs : ¬ (∀ v : ℝ≥0, v ≤ T →
            0 ≤ H ω + (X.X (s + v) ω - X.X s ω)) := by
            intro hh
            apply he
            apply (hEvent ω).mp
            simpa only [H, if_pos ha] using hh
          have hPay : A.indicator f ω = 0 := by
            simp only [Set.indicator_of_mem ha, f, Set.indicator_of_notMem he]
          simpa only [if_neg hs, hPay, ENNReal.ofReal_zero]
      · have hs : ¬ (∀ v : ℝ≥0, v ≤ T →
          0 ≤ H ω + (X.X (s + v) ω - X.X s ω)) := by
          intro hh
          have hz := hh 0 (show (0 : ℝ≥0) ≤ T from zero_le)
          norm_num [H, ha, X.X_zero ω] at hz
        have hPay : A.indicator f ω = 0 := Set.indicator_of_notMem ha _
        simpa only [if_neg hs, hPay, ENNReal.ofReal_zero]
    have hRight :
        (∫⁻ y, ENNReal.ofReal (W y) ∂(Measure.map H P)) =
        ∫⁻ ω, ENNReal.ofReal (A.indicator g ω) ∂P := by
      have hHΩ : Measurable H := hH.mono (𝓕.le s) le_rfl
      calc
        _ = ∫⁻ ω, ENNReal.ofReal (W (H ω)) ∂P := by
          exact lintegral_map (ENNReal.measurable_ofReal.comp hWmeas) hHΩ
        _ = _ := lintegral_congr fun ω => by
          by_cases ha : ω ∈ A
          · simp [H, g, ha, Set.indicator]
          · have hWneg : W (-1) = 0 := hW.1 (-1) (by norm_num)
            simp [H, g, ha, hWneg, Set.indicator]
    have hMasked :
        (∫⁻ ω, ENNReal.ofReal (A.indicator f ω) ∂P) =
        ∫⁻ ω, ENNReal.ofReal (A.indicator g ω) ∂P := by
      calc
        _ = ∫⁻ ω, (if ∀ v : ℝ≥0, v ≤ T → 0 ≤ H ω +
          (X.X (s + v) ω - X.X s ω) then ENNReal.ofReal
            (Real.exp (-(q * (T : ℝ))) *
            W (H ω + (X.X (s + T) ω - X.X s ω)))
          else (0 : ℝ≥0∞)) ∂P := (lintegral_congr hLeft).symm
        _ = ∫⁻ y, ENNReal.ofReal (W y) ∂(Measure.map H P) := hKernel
        _ = _ := hRight
    have hfA : Integrable (A.indicator f) P := hf.indicator hAΩ
    have hgA : Integrable (A.indicator g) P := hg.indicator hAΩ
    have hfA0 : 0 ≤ᵐ[P] A.indicator f :=
      ae_of_all P (fun ω => by
        by_cases ha : ω ∈ A
        · simpa [Set.indicator, ha] using hf0 ω
        · simp [Set.indicator, ha])
    have hgA0 : 0 ≤ᵐ[P] A.indicator g :=
      ae_of_all P (fun ω => by
        by_cases ha : ω ∈ A
        · simpa [Set.indicator, ha] using hg0 ω
        · simp [Set.indicator, ha])
    have hReal :
        (∫ ω, A.indicator g ω ∂P) = ∫ ω, A.indicator f ω ∂P := by
      have h := congrArg ENNReal.toReal (show
          ENNReal.ofReal (∫ ω, A.indicator g ω ∂P) =
          ENNReal.ofReal (∫ ω, A.indicator f ω ∂P) from by
            rw [ofReal_integral_eq_lintegral_ofReal hgA hgA0,
              ofReal_integral_eq_lintegral_ofReal hfA hfA0]
            exact hMasked.symm)
      simpa only [ENNReal.toReal_ofReal (integral_nonneg_of_ae hgA0),
        ENNReal.toReal_ofReal (integral_nonneg_of_ae hfA0)] using h
    simpa only [integral_indicator hAΩ] using hReal

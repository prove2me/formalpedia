-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_unbounded_future_killed_condexp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:52:30.364482+00:00
-- url     : https://prove2.me/submissions/f5c5063e-a644-4ebd-bd31-b92536df99e8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_future_killed_past_test
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_nonneg_past_test_condexp_bridge
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Genuine real conditional killed q-scale semigroup, under explicit
measurability of the actual closed shifted-survival event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (τ : ℕ → ℝ≥0) (s T : ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T)
    (x : ℝ)
    (hB : MeasurableSet {ω : Ω | ∀ v : ℝ≥0, v ≤ T →
      0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)}) :
    P[({ω | ∀ v : ℝ≥0, v ≤ T →
      0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * (T : ℝ))) *
        W ((x + X.X s ω) + (X.X (s + T) ω - X.X s ω))) | 𝓕 s]
      =ᵐ[P] (fun ω => W (x + X.X s ω)) := by
  classical
  let B : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ T →
    0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)}
  let f : Ω → ℝ := B.indicator (fun ω =>
    Real.exp (-(q * (T : ℝ))) *
      W ((x + X.X s ω) + (X.X (s + T) ω - X.X s ω)))
  let g : Ω → ℝ := fun ω => W (x + X.X s ω)
  letI : IsProbabilityMeasure P := X.isProbability
  have hWm : Measurable W :=
    chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hgm : Measurable[𝓕 s] g :=
    hWm.comp (measurable_const.add (X.adapted s))
  have hg : Integrable g P :=
    chat04_unbounded_scale_fixed_time_integrable X q hq W hW hnbv x s
  have hWzero : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  have hWnn (y : ℝ) : 0 ≤ W y := by
    rcases lt_trichotomy y 0 with hy | hy | hy
    · rw [hW.1 y hy]
    · rw [hy, hWzero]
    · exact (scaleFunction_strict_pos_of_unbounded_variation
        X q W hW hnbv y hy).le
  have hgnn : 0 ≤ᵐ[P] g := by
    filter_upwards with ω
    exact hWnn _
  have hfint : Integrable f P := by
    have hRaw : Integrable (fun ω => W (x + X.X (s + T) ω)) P :=
      chat04_unbounded_scale_fixed_time_integrable
        X q hq W hW hnbv x (s + T)
    have hEq : f = B.indicator (fun ω =>
        Real.exp (-(q * (T : ℝ))) * W (x + X.X (s + T) ω)) := by
      funext ω
      have hh : (x + X.X s ω) +
          (X.X (s + T) ω - X.X s ω) = x + X.X (s + T) ω := by
        ring
      by_cases hb : ω ∈ B
      · simp only [f, Set.indicator_of_mem hb]
        rw [hh]
      · simp only [f, Set.indicator_of_notMem hb]
    rw [hEq]
    exact (hRaw.const_mul _).indicator hB
  have hfnn : 0 ≤ᵐ[P] f := by
    filter_upwards with ω
    change 0 ≤ B.indicator (fun ω =>
      Real.exp (-(q * (T : ℝ))) *
        W ((x + X.X s ω) + (X.X (s + T) ω - X.X s ω))) ω
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω]
      exact mul_nonneg (Real.exp_nonneg _) (hWnn _)
    · rw [Set.indicator_of_notMem hω]
  have hTest (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
      (∫⁻ ω, if ω ∈ A then ENNReal.ofReal (f ω)
        else (0 : ℝ≥0∞) ∂P) =
      (∫⁻ ω, if ω ∈ A then ENNReal.ofReal (g ω)
        else (0 : ℝ≥0∞) ∂P) := by
    have h := avram_root29_01_unbounded_future_killed_past_test
      X hnbv q hq W hW τ s T hCover hTerminal x A hA
    have hPoint (ω : Ω) :
        ENNReal.ofReal (f ω) =
        (if ∀ v : ℝ≥0, v ≤ T →
          0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)
         then ENNReal.ofReal
           (Real.exp (-(q * (T : ℝ))) *
             W ((x + X.X s ω) + (X.X (s + T) ω - X.X s ω)))
         else 0) := by
      by_cases hp : ∀ v : ℝ≥0, v ≤ T →
          0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)
      · have hb : ω ∈ B := hp
        simp only [f, Set.indicator_of_mem hb, if_pos hp]
      · have hb : ω ∉ B := hp
        simp only [f, Set.indicator_of_notMem hb,
          ENNReal.ofReal_zero, if_neg hp]
    calc
      (∫⁻ ω, if ω ∈ A then ENNReal.ofReal (f ω) else 0 ∂P) =
        (∫⁻ ω, if ω ∈ A then
          (if ∀ v : ℝ≥0, v ≤ T →
            0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)
           then ENNReal.ofReal
             (Real.exp (-(q * (T : ℝ))) *
               W ((x + X.X s ω) + (X.X (s + T) ω - X.X s ω)))
           else 0) else 0 ∂P) := by
          apply lintegral_congr
          intro ω
          by_cases ha : ω ∈ A
          · simpa only [if_pos ha] using hPoint ω
          · simp only [if_neg ha]
      _ = ∫⁻ ω, if ω ∈ A then ENNReal.ofReal (g ω) else 0 ∂P := by
        simpa only [g] using h
  exact avram_root29_01_nonneg_past_test_condexp_bridge
    (𝓕 s) (𝓕.le s) f g hfint hg hgm hfnn hgnn hTest

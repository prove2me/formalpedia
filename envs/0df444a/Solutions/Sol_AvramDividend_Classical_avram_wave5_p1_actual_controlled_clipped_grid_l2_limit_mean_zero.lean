-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_p1_actual_controlled_clipped_grid_l2_limit_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:52:22.829241+00:00
-- url     : https://prove2.me/submissions/22b0017b-0d18-4303-9c16-d82a9245e3bf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalStoppedDerivative_compensatedClippedFiniteGrid_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_actual_probability_l2_stopped_band_limit_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω α ι : Type*} [mΩ : MeasurableSpace Ω] [mα : MeasurableSpace α]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (T : ℝ≥0)
    (S : ℕ → Finset ι) (s t : ℕ → ι → ℝ≥0)
    (hst : ∀ n i, i ∈ S n → s n i ≤ t n i)
    (R : ℕ → ι → ℝ)
    (hR : ∀ n i, i ∈ S n → 0 ≤ R n i)
    (F : ℕ → Ω → ℝ)
    (hF : ∀ n, F n =
      (fun ω => ∑ i ∈ S n,
        max (-K) (min K
          (if s n i ≤ T then
            (Real.exp (-(q * (s n i : ℝ))) *
              deriv w (Function.leftLim
                (fun u : ℝ≥0 =>
                  x + X.X u ω - rightLimit D u ω) (s n i))) *
            (if (s n i : ℝ≥0∞) ≤ ruinTime X x D ω then
              (1 : ℝ) else 0)
          else 0)) *
        (max (-R n i) (min (R n i)
          (X.X (t n i) ω - X.X (s n i) ω)) -
          ∫ η, max (-R n i) (min (R n i)
            (X.X (t n i - s n i) η)) ∂P)))
    (μ : Measure α) (f : α → ℝ) (hf : Measurable f)
    (henergy : ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂μ < ∞)
    (B : ℕ → Set α) (hB : ∀ n, MeasurableSet (B n))
    (hBfinite : ∀ n, μ (B n) < ∞)
    (hBmono : Monotone B) (hBcover : (⋃ n, B n) = Set.univ)
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hRep : ∀ n, (M n : Ω → ℝ) =ᵐ[P] F n)
    (hbound : ∀ m n, m ≤ n →
      dist (M m) (M n) ≤
        (eLpNorm ((B m)ᶜ.indicator f) (2 : ℝ≥0∞) μ).toReal) :
    ∃ Mlimit : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (nhds Mlimit) ∧
      (∫ ω, Mlimit ω ∂P) = 0 := by
  have hsource (n : ℕ) : (∫ ω, F n ω ∂P) = 0 := by
    rw [hF n]
    exact
      AvramDividend.Classical.avram_wave3_04_originalStoppedDerivative_compensatedClippedFiniteGrid_mean_zero
        X x D hD w q K hK T (S n) (s n) (t n) (hst n) (R n) (hR n)
  have hcenter (n : ℕ) : (∫ ω, M n ω ∂P) = 0 := by
    calc
      (∫ ω, M n ω ∂P) = ∫ ω, F n ω ∂P :=
        integral_congr_ae (hRep n)
      _ = 0 := hsource n
  exact
    AvramDividend.Classical.avram_wave4_p1_actual_probability_l2_stopped_band_limit_mean_zero
      P μ f hf henergy B hB hBfinite hBmono hBcover M hbound hcenter

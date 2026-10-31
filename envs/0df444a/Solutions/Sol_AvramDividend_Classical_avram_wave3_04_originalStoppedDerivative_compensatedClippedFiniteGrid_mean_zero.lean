-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_originalStoppedDerivative_compensatedClippedFiniteGrid_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:05:52.317104+00:00
-- url     : https://prove2.me/submissions/650182d5-22a8-4766-8daf-e54cd1cb65a1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalSource_stoppedClippedFiniteGrid_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_bounded_futurePayoff_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact finite-grid zero mean for stopped discounted original Lévy
verification coefficients and compensated clipped source increments,
with no existence assumption on any untruncated first moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (T : ℝ≥0) (S : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (R : ι → ℝ) (hR : ∀ i ∈ S, 0 ≤ R i) :
    (∫ ω, ∑ i ∈ S,
      max (-K) (min K
        (if s i ≤ T then
          (Real.exp (-(q * (s i : ℝ))) *
            deriv w (Function.leftLim
              (fun u : ℝ≥0 =>
                x + X.X u ω - rightLimit D u ω) (s i))) *
          (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then
            (1 : ℝ) else 0)
        else 0)) *
      (max (-R i) (min (R i) (X.X (t i) ω - X.X (s i) ω)) -
        ∫ η, max (-R i) (min (R i) (X.X (t i - s i) η)) ∂P) ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let m : ι → ℝ := fun i =>
    ∫ η, max (-R i) (min (R i) (X.X (t i - s i) η)) ∂P
  let φ : ι → ℝ → ℝ := fun i y =>
    max (-R i) (min (R i) y) - m i
  have hφ : ∀ i ∈ S, Measurable (φ i) := by
    intro i hi
    change Measurable (fun y : ℝ => max (-R i) (min (R i) y) - m i)
    fun_prop
  have hInt : ∀ i ∈ S,
      Integrable (fun ω => φ i (X.X (t i - s i) ω)) P := by
    intro i hi
    have hBound : ∀ y : ℝ,
        ‖max (-R i) (min (R i) y)‖ ≤ R i := by
      intro y
      have hlo : -R i ≤ max (-R i) (min (R i) y) :=
        le_max_left _ _
      have hup : max (-R i) (min (R i) y) ≤ R i :=
        max_le (by linarith [hR i hi]) (min_le_left _ _)
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, hup⟩
    have hRaw := avram_wave3_04_source_bounded_futurePayoff_integrable
      X (t i - s i) (fun y => max (-R i) (min (R i) y))
      (by fun_prop) (R i) hBound
    exact hRaw.sub (integrable_const (m i))
  have hMean : ∀ i ∈ S,
      (∫ ω, φ i (X.X (t i - s i) ω) ∂P) = 0 := by
    intro i hi
    have hRaw : Integrable
        (fun ω => max (-R i) (min (R i) (X.X (t i - s i) ω))) P := by
      have hh := hInt i hi
      exact (hh.add (integrable_const (m i))).congr
        (Filter.Eventually.of_forall (by intro ω; dsimp [φ]; ring))
    change (∫ ω, max (-R i) (min (R i) (X.X (t i - s i) ω)) -
        m i ∂P) = 0
    rw [integral_sub hRaw (integrable_const (m i))]
    simp [m]
  have hsum := avram_wave3_04_originalSource_stoppedClippedFiniteGrid_mean_zero
    X x D hD w q K hK T S s t hst φ hφ hInt hMean
  simpa only [φ, m] using hsum

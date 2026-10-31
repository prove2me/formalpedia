-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_originalSource_stoppedClippedFiniteGrid_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T17:22:09.487228+00:00
-- url     : https://prove2.me/submissions/ab27bd9f-f3b8-48fc-8843-89e8314f8c05

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalLevy_finiteGrid_centeredPayoff_sum_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact finite-grid zero expectation of the actual original Lévy
controlled-reserve derivative, clipped and stopped at ruin and horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (T : ℝ≥0) (S : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (φ : ι → ℝ → ℝ)
    (hφ : ∀ i ∈ S, Measurable (φ i))
    (hInt : ∀ i ∈ S, Integrable
      (fun ω => φ i (X.X (t i - s i) ω)) P)
    (hmean : ∀ i ∈ S,
      (∫ ω, φ i (X.X (t i - s i) ω) ∂P) = 0) :
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
      φ i (X.X (t i) ω - X.X (s i) ω) ∂P) = 0 := by
  let Z : ℝ≥0 → Ω → ℝ := fun u ω =>
    if u ≤ T then
      (Real.exp (-(q * (u : ℝ))) *
        deriv w (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)) *
      (if (u : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
    else 0
  have hZ : IsStronglyPredictable 𝓕.rightCont Z :=
    avram_wave3_04_source_stopped_discounted_deriv_predictable
      X x D hD w q T
  have hClip := avram_wave3_04_clipped_stronglyPredictable_bounded
    Z hZ K hK
  obtain ⟨Y, hYX, _, _, _⟩ := levy_rightCont_process X
  have hIntY : ∀ i ∈ S,
      Integrable (fun ω => φ i (Y.X (t i - s i) ω)) P := by
    intro i hi
    simpa only [hYX] using hInt i hi
  have hmeanY : ∀ i ∈ S,
      (∫ ω, φ i (Y.X (t i - s i) ω) ∂P) = 0 := by
    intro i hi
    simpa only [hYX] using hmean i hi
  have hEq := avram_wave3_04_originalLevy_finiteGrid_centeredPayoff_sum_zero
    Y S s t hst φ hφ
    (fun i ω => max (-K) (min K (Z (s i) ω)))
    (by
      intro i hi
      exact hClip.1.stronglyAdapted (s i))
    (fun _ => K)
    (by
      intro i hi ω
      exact hClip.2 (s i) ω)
    hIntY hmeanY
  simpa only [hYX] using hEq

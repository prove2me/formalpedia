-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_controlledReserveDiscountedGradient_centeredFiniteGrid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T17:31:44.432926+00:00
-- url     : https://prove2.me/submissions/09d6be89-1a2e-4a36-b064-dbf07a38cc6b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_discounted_deriv_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalLevy_finiteGrid_centeredPayoff_sum_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The discounted gradient sampled at every cell of a genuinely controlled
original Lévy path has zero expected centred finite-grid stochastic sum after
uniform localisation. The right-continuous Lévy reconstruction has identical
sample paths and filtration history, preserving the actual dividend control. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (S : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (φ : ι → ℝ → ℝ)
    (hφ : ∀ i ∈ S, Measurable (φ i))
    (hInt : ∀ i ∈ S, Integrable
      (fun ω => φ i (X.X (t i - s i) ω)) P)
    (hmean : ∀ i ∈ S,
      (∫ ω, φ i (X.X (t i - s i) ω) ∂P) = 0) :
    (∫ ω, ∑ i ∈ S,
      max (-K) (min K (Real.exp (-(q * (s i : ℝ))) *
        deriv w (Function.leftLim
          (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i)))) *
      φ i (X.X (t i) ω - X.X (s i) ω) ∂P) = 0 := by
  let Z : ℝ≥0 → Ω → ℝ := fun u ω =>
    Real.exp (-(q * (u : ℝ))) *
      deriv w (Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)
  have hR :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD
  have hZ : IsStronglyPredictable 𝓕.rightCont Z :=
    avram_wave3_04_discounted_deriv_stronglyPredictable
      (fun u ω => Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)
      hR w q
  have hClip := avram_wave3_04_clipped_stronglyPredictable_bounded
    Z hZ K hK
  let H : ι → Ω → ℝ :=
    fun i ω => max (-K) (min K (Z (s i) ω))
  have hH : ∀ i ∈ S, StronglyMeasurable[𝓕.rightCont (s i)] (H i) := by
    intro i hi
    exact hClip.1.stronglyAdapted (s i)
  have hBound : ∀ i ∈ S, ∀ ω, ‖H i ω‖ ≤ K := by
    intro i hi ω
    exact hClip.2 (s i) ω
  obtain ⟨Y, hYX, _, _, _⟩ := levy_rightCont_process X
  have hIntY : ∀ i ∈ S, Integrable
      (fun ω => φ i (Y.X (t i - s i) ω)) P := by
    intro i hi
    simpa only [hYX] using hInt i hi
  have hmeanY : ∀ i ∈ S,
      (∫ ω, φ i (Y.X (t i - s i) ω) ∂P) = 0 := by
    intro i hi
    simpa only [hYX] using hmean i hi
  have hGrid :=
    avram_wave3_04_originalLevy_finiteGrid_centeredPayoff_sum_zero
      Y S s t hst φ hφ H hH (fun _ => K) (by
        intro i hi ω
        exact hBound i hi ω) hIntY hmeanY
  simpa only [hYX] using hGrid

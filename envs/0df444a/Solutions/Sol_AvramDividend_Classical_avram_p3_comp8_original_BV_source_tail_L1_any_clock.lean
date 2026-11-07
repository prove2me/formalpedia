-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp8_original_BV_source_tail_L1_any_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:20:40.585202+00:00
-- url     : https://prove2.me/submissions/576033bf-54bf-4f1b-b667-7e90f7e81252

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_mass_integrable_any_clock
import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Metric AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The authentic BV source-mass first moment on shrinking complements of
an a.e. exhausting measurable localisation tends to zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (K : ℝ) (hK : 0 ≤ K)
    (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hExhaust : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) :
    (∀ n, Integrable
      (fun ω => if ω ∈ s n then 0 else
        K * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|)) P) ∧
    Tendsto (fun n => ∫ ω, if ω ∈ s n then 0 else
        K * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|) ∂P)
      atTop (nhds (0 : ℝ)) := by
  let H : Ω → ℝ := fun ω =>
    K * (|X.drift| * (T : ℝ) +
      |(T : ℝ) * X.drift - X.X T ω|)
  have hB : Integrable (fun ω =>
      |X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|) P :=
    (avram_p3_comp8_original_BV_source_mass_integrable_any_clock
      X hX hBV T).1
  have hH : Integrable H P := hB.const_mul K
  have hHnonneg (ω : Ω) : 0 ≤ H ω := by
    dsimp [H]
    positivity
  have hInt (n : ℕ) :
      Integrable (fun ω => if ω ∈ s n then 0 else H ω) P := by
    have hEq :
        (fun ω => if ω ∈ s n then 0 else H ω) =
        (s n)ᶜ.indicator H := by
      funext ω
      by_cases hω : ω ∈ s n <;> simp [Set.indicator, hω]
    rw [hEq]
    exact MeasureTheory.Integrable.indicator hH (hs n).compl
  have hDom (n : ℕ) :
      ∀ᵐ ω ∂P, ‖if ω ∈ s n then 0 else H ω‖ ≤ H ω := by
    filter_upwards [] with ω
    by_cases hω : ω ∈ s n
    · simp [hω, hHnonneg ω]
    · simp [hω, Real.norm_eq_abs, abs_of_nonneg (hHnonneg ω)]
  have hAE : ∀ᵐ ω ∂P,
      Tendsto (fun n => if ω ∈ s n then 0 else H ω)
        atTop (nhds (0 : ℝ)) := by
    filter_upwards [hExhaust] with ω hω
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hω
    refine ⟨N, ?_⟩
    intro n hn
    simp [hN n hn, hε]
  refine ⟨hInt, ?_⟩
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence H
    (fun n => (hInt n).aestronglyMeasurable) hH hDom hAE
  simpa only [integral_zero] using hDCT

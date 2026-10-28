-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unconditional_history_future_path_markov_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:09:17.192303+00:00
-- url     : https://prove2.me/submissions/fd613789-2857-4453-bc03-a6bccbc43e73

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Process.Basic
import Theorems.Thm_AvramDividend_Classical_levy_deterministicTime_history_future_product_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Stationary Markov–Tonelli factorisation for the entire future Lévy path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (f : E × (ℝ≥0 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (H ω,
        (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) ∂P) =
    ∫⁻ h, ∫⁻ y, f (h, y)
      ∂(Measure.map (fun ω => (fun t : ℝ≥0 => X.X t ω)) P)
      ∂(Measure.map H P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (s + t) ω - X.X s ω
  let Z : Ω → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  have hHm : Measurable H := hH.mono (𝓕.le s) le_rfl
  have hYm : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro t
    have ht : Measurable (X.X (s + t)) :=
      (X.adapted (s + t)).mono (𝓕.le (s + t)) le_rfl
    exact ht.sub ((X.adapted s).mono (𝓕.le s) le_rfl)
  have hZm : Measurable Z := by
    apply measurable_pi_iff.mpr
    intro t
    exact (X.adapted t).mono (𝓕.le t) le_rfl
  have hJoint :
      Measure.map (fun ω => (H ω, Y ω)) P =
        (Measure.map H P).prod (Measure.map Z P) :=
    levy_deterministicTime_history_future_product_law X s H hH
  calc
    (∫⁻ ω, f (H ω, Y ω) ∂P) =
        ∫⁻ z, f z ∂(Measure.map (fun ω => (H ω, Y ω)) P) := by
          symm
          exact MeasureTheory.lintegral_map hf (hHm.prodMk hYm)
    _ = ∫⁻ z, f z ∂((Measure.map H P).prod (Measure.map Z P)) := by
          rw [hJoint]
    _ = ∫⁻ h, ∫⁻ y, f (h, y) ∂(Measure.map Z P) ∂(Measure.map H P) :=
          MeasureTheory.lintegral_prod f hf.aemeasurable

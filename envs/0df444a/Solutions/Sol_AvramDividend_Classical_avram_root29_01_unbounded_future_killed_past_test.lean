-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_unbounded_future_killed_past_test
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:28:12.31831+00:00
-- url     : https://prove2.me/submissions/52899890-b8c6-4cc2-8e4f-a661967b55db

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_original_future_kernel_past_test
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_original_grid_killed_kernel_scale
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_killed_scale_payoff_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Actual P-law killed q-scale future history tests against every past event,
with genuine Lévy increments, all real reserves and continuous survival. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (τ : ℕ → ℝ≥0)
    (s T : ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T)
    (x : ℝ) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫⁻ ω, if ω ∈ A then
      (if ∀ v : ℝ≥0, v ≤ T →
          0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)
        then ENNReal.ofReal
          (Real.exp (-(q * (T : ℝ))) *
            W ((x + X.X s ω) + (X.X (s + T) ω - X.X s ω)))
        else (0 : ℝ≥0∞))
      else (0 : ℝ≥0∞) ∂P) =
    ∫⁻ ω, if ω ∈ A then ENNReal.ofReal (W (x + X.X s ω))
      else (0 : ℝ≥0∞) ∂P := by
  classical
  let H : Ω → ℝ := fun ω => x + X.X s ω
  let Y : Ω → (ℝ≥0 → ℝ) :=
    fun ω v => X.X (s + v) ω - X.X s ω
  let M : Measure (ℝ≥0 → ℝ) :=
    Measure.map (fun ζ => (fun v : ℝ≥0 => X.X v ζ)) P
  let K : ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞ := fun z =>
    if ∀ j : ℕ, τ j ≤ T → 0 ≤ z.1 + z.2 (τ j)
    then ENNReal.ofReal
      (Real.exp (-(q * (T : ℝ))) * W (z.1 + z.2 T))
    else 0
  have hH : Measurable[𝓕 s] H :=
    measurable_const.add (X.adapted s)
  have hWm : Measurable W :=
    chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hK : Measurable K :=
    chat04_countable_shifted_killed_scale_payoff_measurable τ T T q W hWm
  have hEq (ω : Ω) :
      (∀ v : ℝ≥0, v ≤ T → 0 ≤ H ω + Y ω v) ↔
      (∀ j : ℕ, τ j ≤ T → 0 ≤ H ω + Y ω (τ j)) :=
    chat04_random_reserve_shifted_closed_survival_schedule_iff
      X H ω s T τ hCover hTerminal
  have hTest :=
    avram_root29_01_original_future_kernel_past_test
      X s H hH A hA K hK
  change (∫⁻ ω, (if ω ∈ A then K (H ω, Y ω) else 0) ∂P) =
      (∫⁻ ω, (if ω ∈ A then
        ∫⁻ y, K (H ω, y) ∂M else 0) ∂P) at hTest
  calc
    (∫⁻ ω, if ω ∈ A then
      (if ∀ v : ℝ≥0, v ≤ T → 0 ≤ H ω + Y ω v then
        ENNReal.ofReal
          (Real.exp (-(q * (T : ℝ))) * W (H ω + Y ω T))
        else (0 : ℝ≥0∞)) else 0 ∂P) =
      ∫⁻ ω, if ω ∈ A then K (H ω, Y ω) else 0 ∂P := by
        apply lintegral_congr
        intro ω
        by_cases ha : ω ∈ A
        · simp only [if_pos ha]
          by_cases hs : ∀ v : ℝ≥0, v ≤ T → 0 ≤ H ω + Y ω v
          · simp only [if_pos hs, K, if_pos ((hEq ω).mp hs)]
          · simp only [if_neg hs, K, if_neg (fun hg => hs ((hEq ω).mpr hg))]
        · simp only [if_neg ha]
    _ = ∫⁻ ω, if ω ∈ A then (∫⁻ y, K (H ω, y) ∂M) else 0 ∂P :=
      hTest
    _ = ∫⁻ ω, if ω ∈ A then ENNReal.ofReal (W (H ω)) else 0 ∂P := by
      apply lintegral_congr
      intro ω
      by_cases ha : ω ∈ A
      · simp only [if_pos ha]
        exact avram_root29_01_original_grid_killed_kernel_scale
          X q hq W hW hnbv τ T hCover hTerminal (H ω)
      · simp only [if_neg ha]

-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:00:45.950855+00:00
-- url     : https://prove2.me/submissions/5a498539-1775-40b4-95d2-cf907344a34a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_original_future_kernel_past_test

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The literal original jump count is future-independent once a measurable
same-path future-increment extractor has been supplied. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hExtract : ∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) =
      F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
    P A * (∫⁻ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) := by
  classical
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B)
  let Y : Ω → (ℝ≥0 → ℝ) := fun ω v => X.X (s + v) ω - X.X s ω
  let rate : ℝ≥0∞ :=
    ∫⁻ y, F y ∂(Measure.map (fun ζ : Ω => fun v : ℝ≥0 => X.X v ζ) P)
  haveI : IsProbabilityMeasure P := X.isProbability
  have hH : Measurable[𝓕 s] (fun _ : Ω => ()) := measurable_const
  have hf : Measurable (fun p : Unit × (ℝ≥0 → ℝ) => F p.2) :=
    hF.comp measurable_snd
  have hKernel (C : Set Ω) (hC : MeasurableSet[𝓕 s] C) :
      (∫⁻ ω, (if ω ∈ C then F (Y ω) else 0) ∂P) =
      (∫⁻ ω, (if ω ∈ C then rate else 0) ∂P) := by
    simpa [Y, rate] using
      (avram_root29_01_original_future_kernel_past_test
        X s (fun _ : Ω => ()) hH C hC
        (fun p : Unit × (ℝ≥0 → ℝ) => F p.2) hf)
  have hAll : (∫⁻ ω, F (Y ω) ∂P) = rate := by
    simpa using hKernel Set.univ (MeasurableSet.univ)
  have hAg : MeasurableSet A := (𝓕.le s) A hA
  have hEvent :
      (∫⁻ ω in A, F (Y ω) ∂P) =
      (∫⁻ ω, (if ω ∈ A then F (Y ω) else 0) ∂P) := by
    exact (lintegral_indicator hAg (fun ω => F (Y ω))).symm
  have hConst :
      (∫⁻ ω, (if ω ∈ A then rate else 0) ∂P) = P A * rate := by
    calc
      _ = ∫⁻ ω in A, rate ∂P :=
        lintegral_indicator hAg (fun _ : Ω => rate)
      _ = rate * P A := by simp
      _ = P A * rate := mul_comm _ _
  have hFactor :
      (∫⁻ ω in A, F (Y ω) ∂P) =
      P A * (∫⁻ ω, F (Y ω) ∂P) := by
    rw [hEvent, hKernel A hA, hConst, hAll]
  change (∫⁻ ω in A, N ω ∂P) = P A * (∫⁻ ω, N ω ∂P)
  have hL : (∫⁻ ω in A, N ω ∂P) = ∫⁻ ω in A, F (Y ω) ∂P :=
    lintegral_congr (fun ω => hExtract ω)
  have hR : (∫⁻ ω, N ω ∂P) = ∫⁻ ω, F (Y ω) ∂P :=
    lintegral_congr (fun ω => hExtract ω)
  rw [hL, hR]
  exact hFactor

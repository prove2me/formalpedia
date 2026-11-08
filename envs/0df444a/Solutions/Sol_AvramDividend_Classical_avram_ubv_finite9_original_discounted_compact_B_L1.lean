-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_discounted_compact_B_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T18:02:46.491722+00:00
-- url     : https://prove2.me/submissions/3a6af6df-3493-4360-ab2c-9cd223cb6a8f

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_discounted_compact_stopped_generator_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original discounted generator B of the stopped compensated Taylor budget
has finite expectation in the finite-cap compact-interior case. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D)
    (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u v δ : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C.toReal) (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let E : Set (ℝ≥0 × Ω) := {p | Y p ∈ Icc (u + δ) v}
    let B : Ω → ℝ := fun ω => ∫ t : ℝ≥0,
      (if (t, ω) ∈ E then
        (if t ≤ T then Real.exp (-(q * (t : ℝ))) else 0) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0) *
          (X.generator w (Y (t, ω)) - q * w (Y (t, ω)))
      else 0)
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)
    Integrable B P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hTstop : IsStoppingTime 𝓕.rightCont
      (fun _ => ((T : ℝ≥0) : WithTop ℝ≥0)) :=
    isStoppingTime_const 𝓕.rightCont T
  have hI := avram_ubv_finite9_discounted_compact_stopped_generator_L1
    X x D C hD hC hFinite w hw_smooth hw_cont hw_neg q hq
    hw_gen hw_grad u v δ hu hδ hδone huv hv T (fun _ => T) hTstop
  dsimp only at hI ⊢
  convert hI using 1
  funext ω
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ≤ T
  · by_cases he : (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∈ Icc (u + δ) v
    · simp [ht, he, mul_assoc]
    · simp [ht, he]
  · simp [ht]

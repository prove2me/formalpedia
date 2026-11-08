-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_source_topcap_discounted_compact_stopped_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:14:01.459473+00:00
-- url     : https://prove2.me/submissions/663dc8e4-a662-471f-a51c-318cbce13391

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_discounted_true_clock_compact_generator_hjb_L1_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_predictable_inclusive_sigma_mask_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The discounted original topcap generator is L1 at every true stopped clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D) (hTop : C = ⊤)
    (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (u v δ B : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < B)
    (T : ℝ≥0) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (ρ p * (if Y p ∈ Icc (u + δ) v then
          X.generator w (Y p) - q * w (Y p) else 0))
    Integrable (fun ω => ∫ t : ℝ≥0,
      if t ≤ σ ω then R (t, ω) else 0
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hSmoothB : ContDiffOn ℝ 2 w (Ioo 0 B) := by
    apply hw_smooth.mono
    intro y hy
    exact ⟨hy.1, by simp [hTop]⟩
  have hGenB : ∀ y : ℝ, 0 < y → y < B →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy _
    exact hw_gen y hy (by simp [hTop])
  obtain ⟨μ, _, hμclock, hR, _⟩ :=
    avram_wave5_03_original_discounted_true_clock_compact_generator_hjb_L1_nonpositive
      X x D hD.1.1 w B u v δ hSmoothB hw_cont hw_neg
      hu hδ hδone huv hv q hq T hGenB
  exact avram_ubv_finite9_predictable_inclusive_sigma_mask_L1
    T μ hμclock _ hR σ hσstop

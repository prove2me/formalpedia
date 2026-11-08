-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_family_discounted_terminal_UI
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:02:19.427444+00:00
-- url     : https://prove2.me/submissions/8dc38ae2-9ded-48e4-83d8-c12c78e68e56

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_family_discounted_terminal_uniform_L1
import Theorems.Thm_AvramDividend_Classical_chat03_uniformIntegrable_of_pointwise_bounded_family

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : ℕ → Ω → ℝ≥0) (W Term : ℕ → Ω → ℝ)
    (hW : ∀ k ω, W k ω =
      if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
      else riskProcess X x D (σ k ω) ω)
    (q : ℝ) (hq : 0 ≤ q)
    (hTerm : ∀ k ω, Term k ω =
      Real.exp (-(q * (σ k ω : ℝ))) * w (W k ω))
    (hTermMeas : ∀ k, AEStronglyMeasurable (Term k) P) :
    UniformIntegrable Term (1 : ℝ≥0∞) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨B, hB, hbound, _⟩ :=
    avram_ubv_finite9_original_family_discounted_terminal_uniform_L1
      X x C hfinite hxc w hw_cont hw_neg D hD σ W Term hW q hq hTerm hTermMeas
  let K : ℝ≥0 := ⟨B, hB⟩
  have hbn : ∀ k ω, ‖Term k ω‖₊ ≤ K := by
    intro k ω
    apply (NNReal.coe_le_coe).mp
    change (‖Term k ω‖₊ : ℝ) ≤ B
    simpa only [coe_nnnorm, Real.norm_eq_abs] using hbound k ω
  exact chat03_uniformIntegrable_of_pointwise_bounded_family
    Term hTermMeas K hbn

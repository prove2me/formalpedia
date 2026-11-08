-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_source_topcap_discount_terminal_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:46:12.298885+00:00
-- url     : https://prove2.me/submissions/3a6c11f5-ddaa-4a84-a288-34a52158558d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_topcap_positive_halfline_HJB_bridge
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_positive_halfline_discount_terminal_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (B : ℝ) (hB : 0 < B) (V : Ω → ℝ)
    (hV : ∀ ω, V ω ≤ B) (σ : Ω → ℝ≥0) :
    ∀ ω, 0 ≤ Real.exp (-(q * (σ ω : ℝ))) * w (V ω) ∧
      Real.exp (-(q * (σ ω : ℝ))) * w (V ω) ≤ w B := by
  obtain ⟨hCtwo, _, hGrad⟩ :=
    AvramDividend.Classical.avram_ubv_loc6_topcap_positive_halfline_HJB_bridge
      X w C hTop hw_smooth q hw_gen hw_grad
  have hDiff : DifferentiableOn ℝ w (Ioi 0) :=
    hCtwo.differentiableOn (by norm_num)
  exact AvramDividend.Classical.avram_ubv_top9_positive_halfline_discount_terminal_envelope
    w hw0 hw_cont hw_neg hDiff hGrad B hB V hV q hq σ

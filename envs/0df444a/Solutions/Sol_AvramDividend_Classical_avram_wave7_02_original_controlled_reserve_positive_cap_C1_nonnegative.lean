-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_controlled_reserve_positive_cap_C1_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:58:52.863826+00:00
-- url     : https://prove2.me/submissions/660b6744-9db5-404a-892f-51dc21616aa0

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Under the true Avram controlled reserve, canonical C1 HJB data force candidate nonnegativity at every interior nonnegative reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0), 0 ≤ riskProcess X x D t ω →
      ENNReal.ofReal (riskProcess X x D t ω) < C →
      0 ≤ w (riskProcess X x D t ω) := by
  intro ω t hres hcap
  have hmem : riskProcess X x D t ω ∈
      Icc (0 : ℝ) (riskProcess X x D t ω) :=
    ⟨hres, le_refl _⟩
  exact
    avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
      C hC w hw_cont hw0 hw_smooth hw_grad
      (riskProcess X x D t ω) hres hcap
      (riskProcess X x D t ω) hmem

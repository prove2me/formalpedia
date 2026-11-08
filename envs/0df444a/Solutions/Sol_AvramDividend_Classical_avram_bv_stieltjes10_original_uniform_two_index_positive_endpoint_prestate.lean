-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_stieltjes10_original_uniform_two_index_positive_endpoint_prestate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:59:01.580277+00:00
-- url     : https://prove2.me/submissions/d7f59b2b-ce72-43eb-b775-bd2162b5cc56

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_stieltjes10_original_countable_positive_grid_prejump

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every positive endpoint of every original uniform mesh samples the
true prepayment reserve on one common full-measure event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ᵐ ω ∂P, ∀ n i,
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (u n (i + 1)) =
      riskProcess X x D (u n (i + 1)) ω := by
  rw [ae_all_iff]
  intro n
  have hpos : ∀ i, 0 < u n (i + 1) := by
    intro i
    have hreal : (0 : ℝ) < (u n (i + 1) : ℝ) := by
      rw [huniform n (i + 1)]
      positivity
    exact_mod_cast hreal
  exact avram_bv_stieltjes10_original_countable_positive_grid_prejump
    X x D hD.1.1 (fun i => u n (i + 1)) hpos

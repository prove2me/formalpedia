-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_gaussian_psi_exceeds_any_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:10:37.358449+00:00
-- url     : https://prove2.me/submissions/60602661-0259-43eb-ab25-bfb9783dbd31

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_psi_superlinear_of_positive_sigma
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ) (q : ℝ) :
    ∃ θ : ℝ, 1 ≤ θ ∧ q < X.ψ θ := by
  obtain ⟨β, hβ, hψ⟩ :=
    AvramDividend.Classical.gaussian_psi_superlinear_of_positive_sigma X hσ
      (max q 0 + 1)
  refine ⟨β, hβ, ?_⟩
  have hβpos : 0 < β := by linarith
  have hbase : q ≤ (max q 0 + 1) * β := by
    have hq : q ≤ max q 0 := le_max_left q 0
    have hc : 0 ≤ max q 0 + 1 := by
      have hzero : (0 : ℝ) ≤ max q 0 := le_max_right q 0
      linarith
    have hmul : 0 ≤ (max q 0 + 1) * (β - 1) :=
      mul_nonneg hc (by linarith)
    nlinarith
  exact lt_of_le_of_lt hbase ((lt_div_iff₀ hβpos).mp (hψ β le_rfl))

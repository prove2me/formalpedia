-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_original_shifted_pre_cell_dividend_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:51:14.029703+00:00
-- url     : https://prove2.me/submissions/4831be55-aaf6-45e6-823e-84edc9d04e67

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_chat24_positive_C1_secant
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Finset AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hs : ContDiffOn ℝ 1 w (Ioi 0))
    (hg : ∀ y > 0, 1 ≤ deriv w y) (δ : ℝ) (hδ : 0 < δ)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    D t ω - D s ω ≤
      w (x + δ + X.X t ω - D s ω) - w (riskProcess X x D t ω + δ) := by
  have hU : 0 ≤ riskProcess X x D t ω := by
    by_contra hn
    have hneg : riskProcess X x D t ω < 0 := lt_of_not_ge hn
    exact (not_le_of_gt ht) (iInf_le_of_le t (iInf_le _ hneg))
  have hDmono : D s ω ≤ D t ω := hD.1.1.2.1 ω hst
  have hu : 0 < riskProcess X x D t ω + δ := by linarith
  have huv : riskProcess X x D t ω + δ ≤ x + δ + X.X t ω - D s ω := by
    dsimp only [riskProcess]
    linarith
  have hh := AvramDividend.Classical.avram_chat24_positive_C1_secant w hs hg _ _ hu huv
  dsimp only [riskProcess] at hh ⊢
  linarith

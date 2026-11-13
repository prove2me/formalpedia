-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_ruinstopped_prepayment_compact_allband
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:06:39.084348+00:00
-- url     : https://prove2.me/submissions/5d0cb5af-f55a-4f61-8f92-c0ade8ab24c9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_arbitrary_cofinal_bands_cover_each_fixed_compact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (a b : ℕ → ℝ)
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n))
    (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d)
    (hcC : ENNReal.ofReal c < C) (hdC : ENNReal.ofReal d < C) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (S : ℝ≥0) (ω : Ω) (t : ℝ≥0),
      (t : ℝ≥0∞) ≤ min (ruinTime X x D ω) (S : ℝ≥0∞) →
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t ∈ Icc c d →
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t ∈ Icc (a n) (b n) := by
  obtain ⟨N, hN⟩ :=
    avram_bva_a22_arbitrary_cofinal_bands_cover_each_fixed_compact
      C a b hcover c d hc hcd hcC hdC
  refine ⟨N, ?_⟩
  intro n hn S ω t ht hU
  exact hN n hn hU

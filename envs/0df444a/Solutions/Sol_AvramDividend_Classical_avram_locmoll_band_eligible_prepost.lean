-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_eligible_prepost
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:25:20.160137+00:00
-- url     : https://prove2.me/submissions/af89c69c-b96b-4ae8-a740-6558a7e4d46b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_left_prestate_explicit_source_eq
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_left_limit_cap
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (δ R : ℝ) (hxR : x < R) (θ : Ω → ℝ≥0)
    (hprefix : ∀ ω t, t < θ ω →
      x + X.X t ω - rightLimit D t ω ∈ Icc δ R) :
    ∀ ω s, s ≤ θ ω →
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      riskProcess X x D s ω ∈ Icc 0 R ∧
        x + X.X s ω - rightLimit D s ω ∈ Icc 0 R := by 
  intro ω s hs he
  have hb := avram_p4_e_localise_preruin_postpayment_nonnegative X x C D hD ω s he
  have hd := dividendStrategy_le_rightLimit D hD.1.1 ω s
  have hle : x + X.X s ω - rightLimit D s ω ≤ riskProcess X x D s ω := by
    change x + X.X s ω - rightLimit D s ω ≤ x + X.X s ω - D s ω
    linarith
  have hu : riskProcess X x D s ω ≤ R := by
    by_cases hz : s = 0
    · subst s
      simpa [riskProcess, X.X_zero, hD.1.1.1 ω] using hxR.le
    · have hp : 0 < s := pos_iff_ne_zero.mpr hz
      obtain ⟨l, hl⟩ := X.leftLim ω s hp
      have hleft := avram_p3_2_original_controlled_left_prestate_explicit_source_eq X x D hD.1.1 ω s hp l hl
      have hband := (avram_locmoll_band_left_limit_cap X x C D hD δ R θ hprefix ω s hp hs).1.2
      rw [hleft] at hband
      have hXle := X.noPosJumps ω s l hp hl
      change x + X.X s ω - D s ω ≤ R
      linarith
  exact ⟨⟨hb.trans hle, hu⟩, ⟨hb, hle.trans hu⟩⟩

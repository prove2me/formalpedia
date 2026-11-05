-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_riskProcess_prepost_predictable_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:37:16.088365+00:00
-- url     : https://prove2.me/submissions/4fa16207-407b-4038-b324-f6c3bf0e0aab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepost_reserve_same_leftlim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original pre-payment riskProcess shares the predictable compact
strict-left reserve region at every positive physical time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (a b : ℝ) :
    let E : Set (ℝ≥0 × Ω) := {p |
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    MeasurableSet[𝓕.rightCont.predictable] E ∧
    ∀ (ω : Ω) (t : ℝ≥0), 0 < t →
      ((t, ω) ∈ E ↔ Function.leftLim
        (fun s : ℝ≥0 => riskProcess X x D s ω) t ∈ Icc a b) := by
  constructor
  · exact avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
      X x D hD a b
  · intro ω t ht
    change (Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∈ Icc a b) ↔
      (Function.leftLim (fun s : ℝ≥0 => riskProcess X x D s ω) t ∈ Icc a b)
    rw [avram_wave4_p2_original_prepost_reserve_same_leftlim X x D hD ω t ht]

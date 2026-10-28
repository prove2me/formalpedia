-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_preUpcrossing_ruin_iff_rawDowncrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:51:22.51065+00:00
-- url     : https://prove2.me/submissions/997aaf16-5b64-4f28-91d2-5402db412869

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_prethreshold_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_before_upcrossing
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Before upper exit, controlled ruin occurs precisely when the raw
    Lévy process falls below the negative initial capital. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    ∀ t : ℝ≥0, t < u →
      (riskProcess X x (barrierStrategy X x a) t ω < 0 ↔
        X.X t ω < -x) := by
  intro t ht
  have hbelow : ∀ s : ℝ≥0, s ≤ t → X.X s ω ≤ a - x := by
    intro s hst
    exact firstUpcrossing_prethreshold_le X (a - x) ω u hu s
      (lt_of_le_of_lt hst ht)
  have hzero := barrierStrategy_zero_before_upcrossing X x a t ω hbelow
  simp only [riskProcess, hzero, sub_zero]
  constructor <;> intro h <;> linarith

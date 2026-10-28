-- Prove2me | solution 1 for AvramDividend.Classical.barrierFuturePaymentTimes_mono
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:12:41.93339+00:00
-- url     : https://prove2.me/submissions/e5163d33-d18f-457f-89fd-a9f4927f447d

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {σ τ : ℝ≥0∞} (hστ : σ ≤ τ) :
    paymentTimes σ ⊆ paymentTimes τ := by
  rintro t ⟨h0, h | h⟩
  · exact ⟨h0, Or.inl h⟩
  · exact ⟨h0, Or.inr (lt_of_lt_of_le h hστ)⟩

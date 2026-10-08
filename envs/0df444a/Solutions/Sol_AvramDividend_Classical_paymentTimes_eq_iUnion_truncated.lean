-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_eq_iUnion_truncated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T10:06:25.535823+00:00
-- url     : https://prove2.me/submissions/4508111d-c81f-481d-a74a-3b3fa9c73866

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (σ : ℝ≥0∞) :
    paymentTimes σ = ⋃ n : ℕ, paymentTimes σ ∩ Iic (n : ℝ) := by
  ext t
  constructor
  · intro ht
    obtain ⟨n, hn⟩ := exists_nat_ge t
    exact Set.mem_iUnion.2 ⟨n, ⟨ht, hn⟩⟩
  · intro ht
    rcases Set.mem_iUnion.1 ht with ⟨n, hn⟩
    exact hn.1

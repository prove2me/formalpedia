-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_iUnion_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:39:35.737276+00:00
-- url     : https://prove2.me/submissions/832b5212-f102-4408-8424-9004d33204d4

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (σ : ℝ≥0∞) :
    (⋃ n : ℕ, paymentTimes σ ∩ Iic (n : ℝ)) = paymentTimes σ := by
  ext t
  constructor
  · intro ht
    rcases mem_iUnion.mp ht with ⟨n, htn⟩
    exact htn.1
  · intro ht
    obtain ⟨n, htn⟩ := exists_nat_ge t
    exact mem_iUnion.mpr ⟨n, ⟨ht, htn⟩⟩

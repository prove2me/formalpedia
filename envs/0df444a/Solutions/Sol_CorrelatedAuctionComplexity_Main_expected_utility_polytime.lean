-- Prove2me | solution 1 for CorrelatedAuctionComplexity.Main.expected_utility_polytime
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T07:06:40.072139+00:00
-- url     : https://prove2.me/submissions/850bbb10-92f4-46e4-a3e5-85e9fe30c76e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CorrelatedAuctionComplexity_Main_utilityQ_eq_tie_dp
import Theorems.Thm_CorrelatedAuctionComplexity_Main_tie_dp_polytime

set_option autoImplicit false

open CorrelatedAuctionComplexity.Main
open scoped BigOperators

theorem solution :
    ∃ f : Bits → Bits, CookPvsNP.PolyTimeComputable f ∧
      ∀ (n : ℕ) (H : HDFPA (Fin n)), H.WellFormed 1 →
        ∀ (σ : H.RatProfile), H.Legal (H.realProfile σ) → ∀ i : Fin n,
          f (utilityRequest H σ i) = encodeRat (H.utilityQ σ i) ∧
            (H.utilityQ σ i : ℝ) = H.utility (H.realProfile σ) i := by
  obtain ⟨f, hf, hout⟩ := CorrelatedAuctionComplexity.Main.tie_dp_polytime
  refine ⟨f, hf, fun n H _ σ _ i => ⟨?_, ?_⟩⟩
  · rw [hout n H σ i, ← CorrelatedAuctionComplexity.Main.utilityQ_eq_tie_dp H σ i]
  · simp only [HDFPA.utilityQ, HDFPA.utility, HDFPA.edgeUtility, expectation,
      AGT.profileProb, HDFPA.realProfile, Rat.cast_sum, Rat.cast_mul, Rat.cast_prod]

-- Prove2me | solution 2 for CorrelatedAuctionComplexity.Main.expected_utility_polytime
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T08:34:58.679682+00:00
-- url     : https://prove2.me/submissions/3ed3c646-688e-4130-a6ed-c5668e7f3d4c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CorrelatedAuctionComplexity_Main_utilityQ_eq_tie_dp_legal
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
  refine ⟨f, hf, fun n H _ σ hσ i => ⟨?_, ?_⟩⟩
  · rw [hout n H σ i, ← CorrelatedAuctionComplexity.Main.utilityQ_eq_tie_dp_legal H σ hσ i]
  · simp only [HDFPA.utilityQ, HDFPA.utility, HDFPA.edgeUtility, expectation,
      AGT.profileProb, HDFPA.realProfile, Rat.cast_sum, Rat.cast_mul, Rat.cast_prod]

-- Prove2me | solution 1 for Erdos287.max_gap_three_through_main2_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T10:48:14.983526+00:00
-- url     : https://prove2.me/submissions/aa65313c-915d-4ad3-a1aa-f40618970a98

import Mathlib
import Theorems.Thm_Erdos287_max_gap_three_through_382613443
import Theorems.Thm_Erdos287_gap_three_in_compact_main2_band

set_option autoImplicit false

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hbound : f (k - 1) ≤ 858988211239796718174213) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  by_cases hsmall : f (k - 1) ≤ 382613443
  · exact Erdos287.max_gap_three_through_382613443 k hk f hf1 hmono hsum hsmall
  · exact Erdos287.gap_three_in_compact_main2_band k hk f hf1 hmono hsum (by omega) hbound


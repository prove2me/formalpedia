-- Prove2me | solution 1 for Erdos287.wide_endpoint_ratio_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T11:08:20.373569+00:00
-- url     : https://prove2.me/submissions/394af264-0bf0-4c88-8a28-630d422e1dcb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Erdos287_max_gap_three_through_main3_endpoint
import Theorems.Thm_Erdos287_wide_endpoint_ratio_above_main3

open Finset

set_option autoImplicit false
set_option maxRecDepth 10000

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (hlarge : 382613443 < f (k - 1))
    (hwide : 739 * f 0 < 250 * f (k - 1)) : False := by
  by_cases hfinite : f (k - 1) ≤ 381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435
  · obtain ⟨i, hi, hgi⟩ := Erdos287.max_gap_three_through_main3_endpoint k hk f hf1 hmono hsum hfinite
    have hi' := hgap i hi
    omega
  have hlarge' : 381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435 < f (k - 1) := by omega
  exact Erdos287.wide_endpoint_ratio_above_main3 k hk f hf1 hmono hsum hgap hlarge' hwide


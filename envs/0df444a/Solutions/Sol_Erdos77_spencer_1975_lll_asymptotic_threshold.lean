-- Prove2me | solution 1 for Erdos77.spencer_1975_lll_asymptotic_threshold
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T14:06:46.059292+00:00
-- url     : https://prove2.me/submissions/c9bc4b4a-0ad7-401e-862c-a90ee9b94e04
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Erdos77_spencer_1975_threshold_eventual_size
import Theorems.Thm_Erdos77_spencer_1975_threshold_lll_estimate

open Filter

theorem solution (ε : Real) (hε : 0 < ε) (hε1 : ε < 1) :
    Filter.Eventually (fun k : Nat =>
      2 ≤ k ∧
        k ≤ Nat.floor
          ((1 - ε) * (Real.sqrt 2 / Real.exp 1) * (k : Real) *
            (2 : Real) ^ ((k : Real) / 2)) ∧
        (4 : Real) * (Nat.choose k 2 : Real) *
            (Nat.choose
              (Nat.floor
                ((1 - ε) * (Real.sqrt 2 / Real.exp 1) * (k : Real) *
                  (2 : Real) ^ ((k : Real) / 2)) - 2)
              (k - 2) : Real) *
            (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) Filter.atTop := by
  have hg := Erdos77.spencer_1975_threshold_eventual_size ε hε hε1
  have hl := Erdos77.spencer_1975_threshold_lll_estimate ε hε hε1
  filter_upwards [hg, hl] with k hk hlk
  exact ⟨hk.1, hk.2, hlk⟩

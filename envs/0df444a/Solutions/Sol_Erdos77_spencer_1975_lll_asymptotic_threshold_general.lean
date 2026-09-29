-- Prove2me | solution 1 for Erdos77.spencer_1975_lll_asymptotic_threshold_general
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T11:56:33.305987+00:00
-- url     : https://prove2.me/submissions/f84d0b0b-f32a-4408-92b6-f8ae4944f326
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Erdos77_spencer_1975_lll_asymptotic_threshold
import Mathlib
open Filter

theorem solution (c : Real) (hc : 0 < c) (hc1 : c < 1) :
    Filter.Eventually (fun k : Nat =>
      2 <= k /\
        k <= Nat.floor
          (c * (Real.sqrt 2 / Real.exp 1) * (k : Real) *
            (2 : Real) ^ ((k : Real) / 2)) /\
        (4 : Real) * (Nat.choose k 2 : Real) *
            (Nat.choose
              (Nat.floor
                (c * (Real.sqrt 2 / Real.exp 1) * (k : Real) *
                  (2 : Real) ^ ((k : Real) / 2)) - 2)
              (k - 2) : Real) *
            (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) Filter.atTop := by
  have hε : 0 < 1 - c := by linarith
  have hε1 : 1 - c < 1 := by linarith
  have h := Erdos77.spencer_1975_lll_asymptotic_threshold (1 - c) hε hε1
  have hc' : (1 : Real) - (1 - c) = c := by ring
  simpa only [hc'] using h
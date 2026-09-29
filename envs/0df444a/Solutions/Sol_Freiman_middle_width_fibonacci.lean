-- Prove2me | solution 1 for Freiman.middle_width_fibonacci
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:33:28.858534+00:00
-- url     : https://prove2.me/submissions/857347e7-0e50-4e7c-b229-d756a4cba1fd

import Theorems.Thm_Freiman_middle_width_fibonacci_from_identity
import Theorems.Thm_Freiman_middle_width_identity
import Theorems.Thm_Freiman_middle_continuant_growth

open Freiman

theorem solution :
    ∀ w : List ℕ+, middleWidth w   ≤   (middleBeta-middleAlpha) / (Nat.fib (w.length+1):ℝ)^2 := by
  exact middle_width_fibonacci_from_identity middle_width_identity middle_continuant_growth

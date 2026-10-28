-- Prove2me | solution 1 for AvramDividend.Classical.pointwise_summable_monotone_tsum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:03:58.436002+00:00
-- url     : https://prove2.me/submissions/fb948d3a-119b-45c2-a950-aff243d8c779

import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical
theorem solution
    (F : ℕ → ℝ → ℝ)
    (hmono : ∀ n : ℕ, Monotone (F n))
    (hsum : ∀ x : ℝ, Summable (fun n : ℕ => F n x)) :
    Monotone (fun x : ℝ => ∑' n : ℕ, F n x) := by 
  intro a b hab
  exact (hsum a).tsum_le_tsum (fun n => hmono n hab) (hsum b)

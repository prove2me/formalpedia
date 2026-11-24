-- Prove2me | solution 1 for FairSelling.TPSset_le_PS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:37:21.336436+00:00
-- url     : https://prove2.me/submissions/ef9a2bd4-7b3b-4c16-a360-f9f7f94d3213

import Mathlib
import Definitions.Def_RequestProject_Selling

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) {t : ℝ} (ht : t ∈ TPSset n v p) :
    t ≤ PS n v p := by
  refine' le_trans ht ( div_le_div_of_nonneg_right ( Finset.sum_le_sum fun g _ => by cases max_cases ( p g ) ( v g ) <;> cases max_cases ( p g ) ( Min.min ( v g ) t ) <;> cases min_cases ( v g ) t <;> linarith ) ( Nat.cast_nonneg _ ) )
end FairSelling

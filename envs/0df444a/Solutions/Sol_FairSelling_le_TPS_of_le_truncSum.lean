-- Prove2me | solution 1 for FairSelling.le_TPS_of_le_truncSum
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T01:35:37.072939+00:00
-- url     : https://prove2.me/submissions/4cd8e85d-622f-49a1-96bc-c2cf26f8e612

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]


theorem solution (v p : G → ℝ) {t : ℝ} (ht : t ≤ truncSum n v p t) :
    t ≤ TPS n v p := by
  have bound (s : ℝ) (hs : s ∈ TPSset n v p) : s ≤ PS n v p := by
    apply le_trans hs
    unfold truncSum PS
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun g _ => max_le_max_left _ (min_le_left _ _)) (Nat.cast_nonneg _)
  exact le_csSup (show BddAbove (TPSset n v p) from ⟨_,fun _ hs => bound _ hs⟩) (show t ∈ TPSset n v p from ht)

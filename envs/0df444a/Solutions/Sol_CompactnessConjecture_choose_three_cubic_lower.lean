-- Prove2me | solution 1 for CompactnessConjecture.choose_three_cubic_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/fe0a5f3c-1bc9-4b84-b7d2-8e6e464bd356

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_choose_three_factorial_identity

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution {t : ℕ} (ht : 3 ≤ t) :
    (t : ℝ) ^ 3 / 27 ≤ (t.choose 3 : ℝ) := by
  have hone : 1 ≤ t := by omega
  have htwo : 2 ≤ t := by omega
  have hidentity := congrArg (fun value : ℕ => (value : ℝ))
    (choose_three_factorial_identity t)
  norm_num [Nat.cast_sub hone, Nat.cast_sub htwo] at hidentity
  have htReal : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hfactor :
      0 ≤ (t : ℝ) * ((t : ℝ) - 3) *
        (7 * (t : ℝ) - 6) := by
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (by linarith))
      (by linarith)
  nlinarith
end CompactnessConjecture

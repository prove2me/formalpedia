-- Prove2me | solution 1 for Formalism.CountingSumsFrames.gram_choose_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:42.592939+00:00
-- url     : https://prove2.me/submissions/6d831950-d346-476a-a8a1-95b9a52d9e71

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrameMultinomialBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Real
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (a' : ℕ) : ∀ n : ℕ,
    (((a' + n).choose n : ℕ) : ℝ) = ∏ j : Fin n, ((a' : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← ih]
    have h := Nat.add_one_mul_choose_eq (a' + n) n
    have h' : ((a' + n : ℝ) + 1) * (((a' + n).choose n : ℕ) : ℝ) =
        (((a' + n + 1).choose (n + 1) : ℕ) : ℝ) * ((n : ℝ) + 1) := by exact_mod_cast h
    rw [show a' + (n + 1) = a' + n + 1 by ring]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [mul_div_assoc', eq_div_iff hn.ne']
    linarith
end Formalism.CountingSumsFrames

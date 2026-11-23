-- Prove2me | solution 1 for Formalism.CountingSumsFrames.weylDim_cons_snoc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:48:17.354096+00:00
-- url     : https://prove2.me/submissions/08719c99-3529-4b17-9c23-731d2f2f1deb

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_WeylDimPosOfAntitone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (m : ℕ) (a b : ℤ) (μ : Fin m → ℤ) :
    weylDim (m + 2) (Fin.cons a (Fin.snoc μ b) : Fin (m + 2) → ℤ) =
      weylDim m μ * (∏ j : Fin m, ((((a - μ j : ℤ)) : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) *
      (∏ j : Fin m, ((((μ j - b : ℤ)) : ℚ) + (m : ℚ) - ((j : ℕ) : ℚ)) / ((m : ℚ) - ((j : ℕ) : ℚ))) *
      (((((a - b : ℤ)) : ℚ) + (m : ℚ) + 1) / ((m : ℚ) + 1)) := by
  unfold weylDim
  simp only [Fin.prod_univ_succ (n := m + 1)]
  simp only [Fin.prod_univ_castSucc (n := m)]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc, Fin.snoc_last, lt_self_iff_false,
    Fin.not_lt_zero, if_false, Fin.succ_pos, if_true, Fin.succ_lt_succ_iff,
    Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
    Fin.val_zero, one_mul, mul_one]
  have hl : ∀ x : Fin m, ¬ (Fin.last m < x.castSucc) := fun x => (Fin.castSucc_lt_last x).asymm
  simp only [hl, if_false, Finset.prod_const_one, mul_one]
  push_cast
  simp only [sub_zero, ← add_assoc, add_sub_add_right_eq_sub, Finset.prod_mul_distrib]
  ring
end Formalism.CountingSumsFrames

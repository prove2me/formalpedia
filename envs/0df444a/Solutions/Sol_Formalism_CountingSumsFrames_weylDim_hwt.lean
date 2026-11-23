-- Prove2me | solution 1 for Formalism.CountingSumsFrames.weylDim_hwt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:33.602327+00:00
-- url     : https://prove2.me/submissions/22d8139b-3472-4f28-921c-255c26ad018b

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_WeylDimPosOfAntitone
import Theorems.Thm_Formalism_CountingSumsFrames_weylDim_cons_snoc
import Theorems.Thm_Formalism_CountingSumsFrames_weylDim_zero

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
theorem _root_.solution (m A B : ℕ) : (weylDim (m + 2) (hwt m A B) : ℝ) =
    (∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) *
    (∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) *
    (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1)) := by
  unfold hwt
  rw [weylDim_cons_snoc, weylDim_zero]
  push_cast
  simp only [sub_zero, sub_neg_eq_add, one_mul, zero_add]
end Formalism.CountingSumsFrames

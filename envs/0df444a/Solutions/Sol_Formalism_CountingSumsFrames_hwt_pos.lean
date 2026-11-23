-- Prove2me | solution 1 for Formalism.CountingSumsFrames.hwt_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:51.900369+00:00
-- url     : https://prove2.me/submissions/46023f8a-c65c-49b1-b892-1da39fefe06a

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_WeylDimPosOfAntitone
import Theorems.Thm_Formalism_CountingSumsFrames_weylDim_hwt
import Theorems.Thm_Formalism_CountingSumsFrames_fin_sub_pos

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
theorem _root_.solution (m A B : ℕ) : 0 < (weylDim (m + 2) (hwt m A B) : ℝ) := by
  rw [weylDim_hwt]
  have h1 : 0 < ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_pos fun j _ => by positivity
  have h2 : 0 < ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_pos fun j _ => by
      have := fin_sub_pos m j
      apply div_pos <;> linarith [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
  have h3 : 0 < ((A : ℝ) + B + m + 1) / ((m : ℝ) + 1) := by positivity
  positivity
end Formalism.CountingSumsFrames

-- Prove2me | solution 1 for Formalism.CountingSumsFrames.weylDim_cwt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:46.143031+00:00
-- url     : https://prove2.me/submissions/8da2214f-93d7-4215-8ba2-e52199491b72

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_WeylDimPosOfAntitone
import Theorems.Thm_Formalism_CountingSumsFrames_weylDim_cons_snoc

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
theorem _root_.solution (m A c B : ℕ) (μ : Fin m → ℤ) : (weylDim (m + 2) (cwt m A c B μ) : ℝ) =
    (weylDim m μ : ℝ) *
    (∏ j : Fin m, ((A : ℝ) + c - (μ j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) *
    (∏ j : Fin m, ((μ j : ℝ) + B + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) *
    (((A : ℝ) + c + B + m + 1) / ((m : ℝ) + 1)) := by
  unfold cwt
  rw [weylDim_cons_snoc]
  push_cast
  simp only [sub_neg_eq_add]
end Formalism.CountingSumsFrames

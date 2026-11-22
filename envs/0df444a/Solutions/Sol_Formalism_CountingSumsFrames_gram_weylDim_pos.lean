-- Prove2me | solution 1 for Formalism.CountingSumsFrames.gram_weylDim_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:42:19.167404+00:00
-- url     : https://prove2.me/submissions/e90b44df-7439-4d5d-8a21-fb6affab7f98

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
theorem _root_.solution (m : ℕ) (μ : Fin m → ℤ) (hμ : Antitone μ) : 0 < weylDim m μ := by
  unfold weylDim
  apply Finset.prod_pos; intro i _
  apply Finset.prod_pos; intro j _
  split_ifs with h
  · have h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast (show (i : ℕ) < (j : ℕ) from h)
    have h2 : μ j ≤ μ i := hμ h.le
    have h3 : ((μ j : ℤ) : ℚ) ≤ ((μ i : ℤ) : ℚ) := by exact_mod_cast h2
    push_cast
    apply div_pos <;> linarith
  · exact one_pos
end Formalism.CountingSumsFrames

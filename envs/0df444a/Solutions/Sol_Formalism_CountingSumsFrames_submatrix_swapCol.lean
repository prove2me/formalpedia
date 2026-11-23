-- Prove2me | solution 1 for Formalism.CountingSumsFrames.submatrix_swapCol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:57.847581+00:00
-- url     : https://prove2.me/submissions/d4c61b19-c8da-41e8-9da4-82d502fc5370

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ExistsNonzeroExchangedMinorHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset Matrix
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution {R : Type} [CommRing R] {r k : ℕ} (h : r ≤ k) (H : Matrix (Fin r) (Fin k) R)
    (i : Fin r) (c : Fin k) :
    H.submatrix id (swapCol r k h i c) = (H.submatrix id (Fin.castLE h)).updateCol i (fun m => H m c) := by
  ext m j
  by_cases hj : j = i
  · subst hj
    simp [swapCol]
  · simp [swapCol, hj]
end Formalism.CountingSumsFrames

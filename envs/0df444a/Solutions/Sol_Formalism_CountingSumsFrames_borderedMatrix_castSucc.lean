-- Prove2me | solution 1 for Formalism.CountingSumsFrames.borderedMatrix_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:17.839661+00:00
-- url     : https://prove2.me/submissions/0309524d-78a1-488b-8e21-16ba5260debc

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds

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
open Finset Matrix
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution {R : Type} [CommRing R] (r : ℕ) (ts : Fin r → R) (u : R)
    (T : Matrix (Fin r) (Fin r) R) (b : Fin r → R) (i : Fin (r + 1)) (j : Fin r) :
    borderedMatrix r ts u T b i (Fin.castSucc j) = borderedMatrix r ts 0 T 0 i (Fin.castSucc j) := by
  cases i using Fin.cases <;> simp [borderedMatrix]
end Formalism.CountingSumsFrames

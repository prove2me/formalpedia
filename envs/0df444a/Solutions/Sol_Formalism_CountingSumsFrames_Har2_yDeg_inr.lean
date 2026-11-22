-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.yDeg_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:30.761514+00:00
-- url     : https://prove2.me/submissions/a07e27ea-83b7-4181-925f-114487d6a09f

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds

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
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution (i : Fin k) : yDeg (Finsupp.single (Sum.inr i : XY k) 1) = 1 := by
  simp [yDeg, Finsupp.single_apply]
end Formalism.CountingSumsFrames.Har2

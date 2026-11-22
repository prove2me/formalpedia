-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.xDeg_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:57.910661+00:00
-- url     : https://prove2.me/submissions/e0f6304b-4a3a-49af-9bfa-0d8d0014fc89

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
theorem _root_.solution (m m' : XY k →₀ ℕ) : xDeg (m + m') = xDeg m + xDeg m' := by
  simp only [xDeg, Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
end Formalism.CountingSumsFrames.Har2

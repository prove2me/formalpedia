-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.yDeg_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:04.267813+00:00
-- url     : https://prove2.me/submissions/7271fcc9-fd0a-4bd6-85f9-adb841932826

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
theorem _root_.solution (m m' : XY k →₀ ℕ) : yDeg (m + m') = yDeg m + yDeg m' := by
  simp only [yDeg, Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
end Formalism.CountingSumsFrames.Har2

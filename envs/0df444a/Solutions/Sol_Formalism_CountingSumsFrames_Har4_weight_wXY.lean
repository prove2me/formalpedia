-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.weight_wXY
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:45.661749+00:00
-- url     : https://prove2.me/submissions/0414a4ca-094c-4b05-bb7e-e59fd98b4bbc

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds

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
open Formalism.CountingSumsFrames.Har4
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution {k : ℕ} (m : XY k →₀ ℕ) : Finsupp.weight (wXY k) m = (xDeg m, yDeg m) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type]
  ext <;> simp [wXY, xDeg, yDeg, Prod.fst_sum, Prod.snd_sum]
end Formalism.CountingSumsFrames.Har4

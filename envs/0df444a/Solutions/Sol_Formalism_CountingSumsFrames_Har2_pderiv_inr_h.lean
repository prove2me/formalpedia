-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.pderiv_inr_h
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:01.301318+00:00
-- url     : https://prove2.me/submissions/6e94ae43-b8a0-4821-9c85-129fc340ad11

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
theorem _root_.solution (i : Fin k) : pderiv (Sum.inr i) (hXY K k) = X (Sum.inl i) := by
  classical
  simp [hXY, Derivation.leibniz, pderiv_X, Pi.single_apply]
end Formalism.CountingSumsFrames.Har2
